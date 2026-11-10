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
 *   compile_attribute_vv_case, compile_attribute_case — Attribute's
 *                           expr_vv_case and expr_sim_case, for
 *                           compile_expr_sim and the body simulation;
 *                           compile_attribute_vv_sim follows
 *   attr_add_frag, attr_add_path, attr_extends, stmt_state_rel_region_lt,
 *   immutable_holds_read, field_ptr_w2n — the offset's fragment and the
 *                           pointer facts, which exprSimTuple shares
 *
 * Helpers: vv_loc, attr_offset, compile_expr_attribute,
 *   eval_expr_attribute, attr_pre_base, attr_add_post, struct_value_shape,
 *   base_vv_holds_struct, base_vv_at_struct, attr_vv_at_field,
 *   sub_layout_field, immutable_holds_field, attr_vv_post
 *
 * Where the base is a local's place memory no longer holds (a popped
 * element), the source reads the field from the popped history, which
 * holds no snapshot at the field itself: its keys end in array indices
 * (expr_sim_inv's popped_keys_indexed, exprSimAttributeFields's
 * popped_keys_indexed_not_at_field).
 *
 * A base in code (an immutable, LocCode) points into an immutable's data:
 * immutable_holds places the base's value inside the immutable's layout
 * (sub_layout), and the field sits inside the base's at its offset.
 *)

Theory exprSimAttribute
Ancestors
  exprSimAttributeProps exprSimFieldLayout exprSimVVFrame
  exprSimSource
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  allocLimits
  list rich_list finite_map pair
  fragExec  exprSimHyps exprSimUnwrap exprSimLen exprSimLeaves
  exprSimBuffer exprSimAggregateChildren exprSimAttributeFields
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv loweringStateRelDefs context
  accountsRelProps
  valueEncoding valueEncodingDefs vyperAST vyperInterpreter vyperState vyperStorage vyperValue
  vyperTyping vyperTypeSystem vyperTypeExprSoundness vyperTypeInvariants
  vyperPlaceResultTyping
  venomState venomInst venomMemDefs
Libs
  pairLib

open gasContextTheory gasOutcomeTheory gasSummaryTheory gasSummaryComposeTheory
     gasExemptCertTheory fragGasModeTheory fragGasPathTheory;

(* ===== The lowering ===== *)

(* The location compile_attribute reads the base's pointer in. *)


(* The offset compile_attribute adds to the base's pointer: slots in storage
   and transient storage, bytes elsewhere. *)


Theorem compile_expr_attribute:
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

Theorem eval_expr_attribute:
  !cx ann obj fld es.
    eval_expr cx (Attribute ann obj fld) es =
    (do r <- eval_expr cx obj;
        select_result cx (expr_type obj) r (AttrSubscript fld) od) es
Proof
  simp[Once evaluate_def]
QED

Theorem attr_pre_base:
  !cenv cx env ann obj fld es.
    expr_body_pre cenv cx env (Attribute ann obj fld) es ==>
    expr_body_pre cenv cx env obj es /\
    ?sid. expr_type obj = StructT sid /\
          attribute_type (get_tenv cx) (StructT sid) fld = SOME ann
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  gvs[expr_body_pre_def, well_typed_expr_def, attribute_type_ok_def,
      vyperTypeCallGraphTheory.int_calls_expr_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm, byte_widths_expr_def,
      alloc_limits_expr_def] >>
  Cases_on `expr_type obj` >> gvs[attribute_type_def] >>
  rpt strip_tac >>
  TRY (qpat_x_assum `~supported_expr_exists _ (Attribute _ _ _)` mp_tac >>
       simp[supportedExprTraverseTheory.supported_expr_exists_def] >> NO_TAC) >>
  qpat_x_assum `!target. supported_expr_exists _ (Attribute _ _ _) ==> _`
    (qspec_then `target` irule) >>
  simp[supportedExprTraverseTheory.supported_expr_exists_def]
QED

Theorem attr_add_post[local]:
  !cenv ty e sa vv sm off dst sn func cx es s0 es' tv s w ctx.
    compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) /\
    vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
    eval_operand (vv_operand vv) s = SOME w ==>
    ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
        vv_post ctx func cenv cx e es sa sn s0 es' tv vv q /\
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
      irule exprSimVVFrameTheory.literal_operand_frame >>
      reverse conj_tac >- simp[update_var_def] >>
      qexists_tac `sm` >> simp[] >>
      rw[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem attr_add_frag:
  !ctx cenv ty e sa vv sm off dst sn func cx es s0 es' tv R.
    compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) ==>
    frag_exec ctx sm sn
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' tv vv s)
      (\s. ?w. vv_post ctx func cenv cx e es sa sn s0 es' tv vv s /\
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

Theorem attr_extends:
  !ops sa p sb. emit_op ADD ops sa = (p, sb) ==> cs_extends sa sb
Proof
  rpt strip_tac >>
  drule emitted_insts_emit_op >> drule emit_op_extends >> rpt strip_tac >>
  irule cs_extends_same_block >>
  gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND3]
QED

(* ===== The value_vv of the field ===== *)



Theorem struct_value_shape:
  !fs v. value_has_type (StructTV fs) v ==>
         ?vals. v = StructV vals /\ struct_has_type fs vals
Proof
  Cases_on `v` >> simp[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> simp[value_has_type_def]
QED

Theorem immutable_holds_read:
  !cenv cx t tv w es s.
    immutable_holds cenv cx t tv w es s ==> ?v. read_result cx tv es = (INL v, es)
Proof
  rw[immutable_holds_def] >> metis_tac[]
QED

(* What the base's value_vv says of the struct it holds, by location. *)
Theorem base_vv_holds_struct[local]:
  !cenv cx sid tv vv es s stv w.
    vv_holds cenv cx (StructT sid) tv vv es s /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME stv /\
    eval_operand (vv_operand vv) s = SOME w ==>
    ?v. read_result cx tv es = (INL v, es) /\
        (vv_loc vv = LocMemory ==> val_in_memory stv v (w2n w) s.vs_memory) /\
        (vv_loc vv = LocStorage ==>
           read_storage_slot cx F w stv es = (INL v, es) /\
           slots_in_range (get_storage cx es F) (w2n w) stv) /\
        (vv_loc vv = LocTransient ==>
           read_storage_slot cx T w stv es = (INL v, es) /\
           slots_in_range (get_storage cx es T) (w2n w) stv) /\
        (vv_loc vv = LocStorage ==>
           storage_range_agree (get_storage cx es F) (contract_storage s)
             w stv) /\
        (vv_loc vv = LocTransient ==>
           storage_range_agree (get_storage cx es T) (contract_transient s)
             w stv) /\
        (vv_loc vv = LocCode ==>
           immutable_holds cenv cx (StructT sid) tv w es s) /\
        vv_loc vv <> LocCalldata
Proof
  rpt gen_tac >> Cases_on `vv` >>
  simp[vv_holds_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_rel_def, is_word_type_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  gvs[storage_holds_def] >> metis_tac[immutable_holds_read]
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
                 b <= w2n w /\ w2n w + val_footprint stv v <= b + sz /\
                 (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
                              b + sz <= lb \/ lb + lsz <= b)) \/
     (?n b sz. local_region cenv es.scopes s n b sz /\
               b <= w2n w /\ w2n w + val_footprint stv v <= b + sz /\
               local_path_at cenv cx n (w2n w - b) stv) \/
     val_footprint stv v = 0)
Proof
  rpt gen_tac >> Cases_on `vv` >>
  simp[vv_at_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_at_def, is_word_type_def, local_val_at_def] >>
  rpt strip_tac >> gvs[] >>
  TRY (first_x_assum drule_all >> strip_tac >> gvs[]) >>
  TRY (qpat_x_assum `evaluate_type _ (StructT _) = SOME (BaseTV _)` mp_tac >>
       simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(), LET_THM] >>
       NO_TAC) >>
  metis_tac[]
QED

(* A field's pointer does not wrap: the struct's bytes end below 2 ** 256,
   or it has none and the field is at offset 0. *)


(* The field's placement in memory, from the base's. *)
Theorem attr_vv_at_field[local]:
  !func cenv cx sid sa sn es1 tv bvv q w dst ann fld fs ftv vals fv tv' ctx.
    stmt_state_rel ctx func cenv cx es1 q /\
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
  all_tac
  >~ [`FLOOKUP q.vs_allocas aid = SOME (b,sz)`]
  >- (disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC)
  >~ [`local_region cenv es1.scopes q n b sz`]
  >- (disj2_tac >> disj1_tac >> qexistsl [`n`, `b`, `sz`] >> simp[] >>
      `mem_step_offset (StructTV fs) (AttrSubscript fld) =
       SOME (struct_field_offset fields fld, ftv)` by
        simp[mem_step_offset_def, mem_field_offset_layout] >>
      drule_all local_path_at_step >>
      `w2n w - b + struct_field_offset fields fld =
       w2n w + struct_field_offset fields fld - b` by decide_tac >>
      simp[local_path_at_val_at] >> decide_tac) >>
  disj2_tac >> disj2_tac >> decide_tac
QED

(* A struct's field sits inside the struct's layout at the field's offset. *)
Theorem sub_layout_field[local]:
  !itv iv k fs vals fields fld ftv fv.
    sub_layout itv iv k (StructTV fs) (StructV vals) /\
    fields_layout fields fs /\ struct_has_type fs vals /\
    ALOOKUP vals fld = SOME fv /\ ALOOKUP fs fld = SOME ftv ==>
    sub_layout itv iv (k + struct_field_offset fields fld) ftv fv
Proof
  rw[sub_layout_def]
  >- (drule_all struct_field_offset_le >> gvs[type_memory_size_def]) >>
  first_x_assum drule >> simp[val_in_memory_def] >> strip_tac >>
  drule_all fields_in_memory_field >> simp[]
QED

(* The field of a struct an immutable's code pointer holds: the pointer
   plus the field's offset. *)
Theorem immutable_holds_field[local]:
  !cenv cx sid tv w es s fs fields vals fld fv ftv ann tv'.
    immutable_holds cenv cx (StructT sid) tv w es s /\
    read_result cx tv es = (INL (StructV vals), es) /\
    fields_layout fields fs /\ ALOOKUP vals fld = SOME fv /\
    ALOOKUP fs fld = SOME ftv /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    evaluate_type (get_tenv cx) ann = SOME ftv /\
    read_result cx tv' es = (INL fv, es) ==>
    immutable_holds cenv cx ann tv' (w + n2w (struct_field_offset fields fld))
      es s
Proof
  rpt strip_tac >>
  `value_has_type (StructTV fs) (StructV vals)` by
    (fs[immutable_holds_def] >> gvs[]) >>
  drule struct_value_shape >> strip_tac >> gvs[] >>
  `value_has_type ftv fv` by
    (drule_all vyperAssignPreservesTypeTheory.struct_field_has_type >>
     strip_tac >> gvs[]) >>
  `sub_layout (StructTV fs) (StructV vals) (struct_field_offset fields fld)
     ftv fv` by
    (qspecl_then [`StructTV fs`, `StructV vals`, `0`, `fs`, `vals`, `fields`,
                  `fld`, `ftv`, `fv`] mp_tac sub_layout_field >>
     simp[sub_layout_def]) >>
  irule immutable_holds_sub >>
  qexistsl [`ftv`, `fv`, `StructTV fs`, `StructV vals`, `StructT sid`, `tv`] >>
  simp[]
QED

Theorem type_widens_to_struct[local]:
  type_widens_to tenv t (StructT sid) ==> t = StructT sid
Proof
  Cases_on `t` >> simp[type_widens_to_def, arg_type_fits_def] >>
  metis_tac[]
QED

Theorem attr_post_value_type:
  expr_body_pre cenv cx env obj es /\ expr_type obj = StructT sid ==>
  post_value_type cenv obj = expr_type obj
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env obj` by
    fs[expr_body_pre_def] >>
  drule_all post_value_type_widens >>
  simp[] >> metis_tac[type_widens_to_struct]
QED

(* The field's value_vv after the ADD, from the base's. *)
Theorem attr_vv_post:
  !func cenv cx obj es sa sn s0 es1 tv bvv q w dst ann fld sid fs ftv tv' ctx.
    vv_post ctx func cenv cx obj es sa sn s0 es1 tv bvv q /\
    post_value_type cenv obj = expr_type obj /\
    eval_operand (vv_operand bvv) q = SOME w /\
    eval_operand dst q =
      SOME (w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld)) /\
    expr_type obj = StructT sid /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    fields_layout
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    ALOOKUP fs fld = SOME ftv /\ evaluate_type (get_tenv cx) ann = SOME ftv /\
    (!v. read_result cx tv es1 = (INL v, es1) ==>
         value_has_type (StructTV fs) v) /\
    (!vals. read_result cx tv es1 = (INL (StructV vals), es1) ==>
       ?fv. ALOOKUP vals fld = SOME fv /\
            read_result cx tv' es1 = (INL fv, es1)) ==>
    vv_post ctx func cenv cx (Attribute ann obj fld) es sa sn s0 es1 tv'
      (LocatedValue ann (mk_ptr dst (vv_loc bvv))) q
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `vv_post ctx _ _ _ obj _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  gvs[] >>
  drule_all base_vv_holds_struct >> strip_tac >>
  `value_has_type (StructTV fs) v` by metis_tac[] >>
  drule struct_value_shape >> strip_tac >> gvs[] >>
  TRY (first_x_assum drule >> strip_tac) >>
  `value_has_type ftv fv` by
    (drule_all vyperAssignPreservesTypeTheory.struct_field_has_type >>
     strip_tac >> gvs[]) >>
  rewrite_tac[vv_post_def] >> simp[] >> rpt conj_tac
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
          simp[wordsTheory.WORD_ADD_0])
      >~ [`immutable_holds`]
      >- (irule immutable_holds_field >> simp[] >> metis_tac[]) >>
      drule struct_field_slot_exists >> strip_tac >>
      drule_all read_storage_slot_field >> strip_tac >> gvs[] >>
      drule_all storage_range_agree_field >> strip_tac >>
      drule_all struct_field_offset_slots_eq >> strip_tac >>
      imp_res_tac vyperLookupStorageTheory.storage_field_slots_in_range >>
      gvs[storage_holds_def])
  >~ [`vv_at _ _ _ _ _ _ _ (LocatedValue _ _) _`]
  >- (simp[expr_type_def] >> irule attr_vv_at_field >> simp[] >>
      metis_tac[])
  >~ [`storage_read_live`]
  >- (strip_tac >>
      qpat_x_assum `~expr_has_effect obj ==> _` mp_tac >>
      asm_rewrite_tac[] >> strip_tac >>
      drule vyperPlaceResultTypingTheory.struct_field_slot_exists >> strip_tac >>
      drule_all exprSimFieldLayoutTheory.struct_field_offset_slots_eq >>
      strip_tac >>
      Cases_on `bvv` >>
      simp[mk_ptr_def, vv_loc_def, contextTheory.vv_location_def] >>
      rename1 `LocatedValue t p` >>
      `t = StructT sid` by
        (qpat_x_assum `vv_holds _ _ _ _ (LocatedValue _ _) _ _` mp_tac >>
         simp[vv_holds_def, is_bytestring_type_def] >> rpt strip_tac >>
         simp[]) >>
      gvs[vv_loc_def, contextTheory.vv_location_def,
          contextTheory.vv_operand_def, attr_offset_def] >>
      rpt strip_tac >> gvs[] >>
      irule accountsRelPropsTheory.storage_read_live_field >>
      metis_tac[]) >>
  first_assum ACCEPT_TAC
QED

(* ===== The simulation ===== *)

Theorem attr_eval_inst_idx[local]:
  !op s n. eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

(* The offset's ADD as a target path with no GAS reads. *)
Theorem attr_add_path:
  !ctx func cenv cx e es ty sa vv sm off dst sn s0 es' tv t.
    compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) /\
    fn_has_code sm sn func /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    vv_post ctx func cenv cx e es sa sm s0 es' tv vv t ==>
    ?t' w. gas_path ctx func t 0 (OK t') /\
      t'.vs_current_bb = sn.cs_current_bb /\
      t'.vs_inst_idx = LENGTH sn.cs_current_insts /\
      vv_post ctx func cenv cx e es sa sn s0 es' tv vv t' /\
      eval_operand (vv_operand vv) t' = SOME w /\
      eval_operand dst t' = SOME (w + n2w off)
Proof
  rpt strip_tac >>
  `?w. eval_operand (vv_operand vv) t = SOME w` by
    (gvs[vv_post_def] >> Cases_on `vv` >>
     gvs[vv_holds_def, vv_operand_def, expr_val_rel_def]) >>
  drule_all attr_add_post >> strip_tac >>
  qspecl_then [`sm`, `sn`, `vv_operand vv`, `dst`, `t`, `w`, `off`] mp_tac
    buffer_emit_add_run >>
  simp[] >> strip_tac >> gvs[] >>
  `sn.cs_current_bb = sm.cs_current_bb /\
   LENGTH sn.cs_current_insts = SUC (LENGTH sm.cs_current_insts)` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qexistsl_tac [`update_var (STRING #"%" (toString sm.cs_next_var))
                   (w + n2w off) t with vs_inst_idx := SUC t.vs_inst_idx`,
                `w`] >>
  simp[attr_eval_inst_idx] >> conj_tac
  >- (qpat_x_assum `emit_op ADD _ _ = _` assume_tac >>
      drule emit_op_zero_path >> simp[is_terminator_def] >>
      disch_then irule >> simp[] >> gen_tac >>
      irule step_ADD >> simp[eval_operand_def]) >>
  simp[] >> simp[update_var_def]
QED

Theorem attr_source[local]:
  !cx ann obj fld.
    eval_expr cx (Attribute ann obj fld) =
    bind (eval_expr cx obj)
      (\r. select_result cx (expr_type obj) r (AttrSubscript fld))
Proof
  simp[FUN_EQ_THM, eval_expr_attribute]
QED

(* The field's selection reads no gas observation. *)
Theorem attr_select_gas_obs[local]:
  !cx ty tv fld ee r.
    select_result cx ty tv (AttrSubscript fld) ee = (r, ee) ==>
    !tail. select_result cx ty tv (AttrSubscript fld)
             (ee with gas_obs := tail) = (r, ee with gas_obs := tail)
Proof
  rpt gen_tac >> Cases_on `tv`
  >~ [`Value v`]
  >- (simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
           return_def, raise_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]))
  >~ [`HashMapRef`] >- simp[select_result_def, extend_place_def, raise_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl`
  >~ [`StoragePlace tr slot ptv`]
  >- (Cases_on `ptv` >>
      simp[select_result_def, extend_place_def, extend_storage_place_def,
           bind_def, lift_option_type_def, return_def, raise_def,
           pairTheory.UNCURRY] >>
      rpt (BasicProvers.FULL_CASE_TAC >>
           gvs[return_def, raise_def, pairTheory.UNCURRY]))
  >~ [`MemoryPlace id path`]
  >- (simp[select_result_def, extend_place_def, place_type_value_def,
           read_place_def, get_scopes_def, bind_def, ignore_bind_def,
           lift_option_type_def, lift_sum_def, return_def, raise_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> simp[bind_def, return_def, raise_def]) >>
      rpt strip_tac >> gvs[]) >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, get_immutables_def, get_address_immutables_def,
       bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> simp[bind_def, return_def, raise_def]) >>
  rpt strip_tac >> gvs[]
QED

Theorem attr_operand_admissible[local]:
  !cenv cx env e es.
    expr_body_pre cenv cx env e es ==>
    gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  rpt strip_tac >> simp[gas_admissible_def] >> rpt strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  metis_tac[expr_body_pre_vv_res_ok]
QED

Theorem attr_exempt_cert[local]:
  !memory tops p cx ann obj fld start marks out endpoint.
    gas_exempt_cert memory tops p (ignore_bind (eval_expr cx obj) (return ()))
      start marks out endpoint ==>
    gas_exempt_cert memory tops p
      (ignore_bind (eval_expr cx (Attribute ann obj fld)) (return ()))
      start marks out endpoint
Proof
  rpt strip_tac >> simp[attr_source] >>
  PairCases_on `p` >> PairCases_on `start` >>
  PairCases_on `out` >> PairCases_on `endpoint` >>
  qmatch_goalsub_abbrev_tac `bind (eval_expr cx obj) sel` >>
  `ignore_bind (bind (eval_expr cx obj) sel) (return ()) =
   bind (eval_expr cx obj) (\r. ignore_bind (sel r) (return ()))` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `eval_expr cx obj x` >> Cases_on `q` >> simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_result >> simp[]
QED

(* The source facts at the base's actual end state. *)
Theorem attr_base_facts[local]:
  !cenv cx env ann obj fld es sid es0 btv es1.
    expr_body_pre cenv cx env (Attribute ann obj fld) es0 /\
    expr_body_pre cenv cx env obj es0 /\ expr_type obj = StructT sid /\
    attribute_type (get_tenv cx) (StructT sid) fld = SOME ann /\
    eval_expr cx obj es0 = (INL btv, es1) ==>
    ?fs ftv.
      evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
      fields_layout
        (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
      ALOOKUP fs fld = SOME ftv /\
      evaluate_type (get_tenv cx) ann = SOME ftv /\
      (!v. read_result cx btv es1 = (INL v, es1) ==>
           value_has_type (StructTV fs) v) /\
      ~popped_at_field btv fld es1 /\
      !res es2.
        select_result cx (StructT sid) btv (AttrSubscript fld) es1 =
          (res, es2) ==> !m. res <> INR (Error (TypeError m))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es0` by fs[expr_body_pre_def] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all attribute_type_evaluates >> strip_tac >> simp[] >>
  conj_tac
  >- (irule popped_keys_indexed_not_at_field >>
      drule_all expr_body_pre_eval_result >> simp[expr_sim_inv_def]) >>
  rpt strip_tac >>
  `eval_expr cx (Attribute ann obj fld) es0 = (res, es2)` by
    simp[eval_expr_attribute, bind_def] >>
  qspecl_then [`cenv`, `cx`, `env`, `Attribute ann obj fld`, `es0`, `res`,
               `es2`] mp_tac expr_body_pre_vv_res_ok >>
  simp[expr_vv_res_ok_def]
QED

(* A completed base execution: the ADD's path and the field's post. *)
Theorem attr_summary_ok[local]:
  !ctx func cenv cx env ty ann obj fld es sid sa sm p sb bvv s0 marks btv fe
   t R.
    expr_body_pre cenv cx env (Attribute ann obj fld) es /\
    expr_body_pre cenv cx env obj es /\ expr_type obj = StructT sid /\
    attribute_type (get_tenv cx) (StructT sid) fld = SOME ann /\
    compile_expr cenv ty obj sa = (bvv, sm) /\ local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [vv_operand bvv;
                 Lit (n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld))]
      sm = (p, sb) /\
    fn_has_code sm sb func /\
    gas_marked_exec F (ctx,func) (eval_expr cx obj) (es,s0) marks
      (INL btv) fe (OK t) /\
    vv_post ctx func cenv cx obj es sa sm s0 (fe with gas_obs := []) btv bvv t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    gas_summary_at F (ctx,func) marks (eval_expr cx (Attribute ann obj fld))
      (es,s0)
      (\res ee t. ?tv. res = INL tv /\
         vv_post ctx func cenv cx (Attribute ann obj fld) es sa sb s0 ee tv
           (LocatedValue ann (mk_ptr p (vv_loc bvv))) t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) R
Proof
  rpt strip_tac >>
  `post_value_type cenv obj = expr_type obj` by
    metis_tac[attr_post_value_type] >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL btv, fe with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  mp_tac (Q.SPECL [`cenv`,`cx`,`env`,`ann`,`obj`,`fld`,`es`,`sid`,
            `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
            `btv`,`fe with gas_obs := []`] attr_base_facts) >>
  simp[] >> strip_tac >>
  drule_all attr_add_path >> strip_tac >>
  rename1 `gas_path ctx func t 0 (OK t1)` >>
  `?v. read_result cx btv (fe with gas_obs := []) =
       (INL v, fe with gas_obs := [])` by
    (qpat_x_assum `vv_post _ _ _ _ obj _ _ sb _ _ _ _ t1` mp_tac >>
     simp[vv_post_def] >> strip_tac >>
     drule_all base_vv_holds_struct >> metis_tac[]) >>
  `value_has_type (StructTV fs) v` by metis_tac[] >>
  drule struct_value_shape >> strip_tac >> gvs[] >>
  Cases_on `select_result cx (StructT sid) btv (AttrSubscript fld)
              (fe with gas_obs := [])` >>
  rename1 `_ = (sres, es2)` >>
  `!m. sres <> INR (Error (TypeError m))` by metis_tac[] >>
  drule_all select_attr_read >> strip_tac >> gvs[] >>
  rename1 `select_result _ _ _ _ _ = (INL tv2, _)` >>
  drule attr_select_gas_obs >> simp[] >> strip_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL tv2`, `fe`, `OK t1`] >> simp[] >> conj_tac
  >- (rewrite_tac[attr_source] >>
      irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
               |> REWRITE_RULE [APPEND_NIL]) >>
      qexistsl_tac [`fe`,`t`,`btv`] >> simp[] >>
      simp[gas_marked_exec_def, gas_marked_path_def, gas_explicit_def]) >>
  disj1_tac >> irule attr_vv_post >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Theorem attr_vv_sim[local]:
  !ctx func cenv cx env ty ann obj fld es sid.
    expr_body_pre cenv cx env (Attribute ann obj fld) es /\
    expr_body_pre cenv cx env obj es /\ expr_type obj = StructT sid /\
    attribute_type (get_tenv cx) (StructT sid) fld = SOME ann /\
    expr_vv_sim ctx func cenv cx ty obj es ==>
    expr_vv_sim ctx func cenv cx ty (Attribute ann obj fld) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  drule compile_expr_attribute >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv ty obj sa = (bvv, sm)` >>
  drule attr_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    metis_tac[attr_operand_admissible] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ obj _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`,`sm`,`bvv`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >> gvs[]
      >- (drule_all attr_summary_ok >> simp[]) >>
      Cases_on `res` >> gvs[] >>
      rename1 `gas_marked_exec _ _ _ _ marks (INR exn) fe fr` >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR exn`,`fe`,`fr`] >> simp[] >>
      rewrite_tac[attr_source] >> irule gas_marked_exec_bind_exception >>
      simp[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[attr_exempt_cert]
QED

Theorem compile_attribute_vv_case:
  !nocalls ctx func cenv cx ann obj fld.
    expr_vv_case nocalls ctx func cenv cx obj ==>
    expr_vv_case nocalls ctx func cenv cx (Attribute ann obj fld)
Proof
  rpt gen_tac >> strip_tac >> simp[Once expr_vv_case_def] >>
  rpt gen_tac >> strip_tac >>
  drule attr_pre_base >> strip_tac >>
  `post_value_type cenv obj = expr_type obj` by
    (drule_all attr_post_value_type >> simp[]) >>
  `expr_vv_sim ctx func cenv cx ty obj es` by
    (irule (iffLR expr_vv_case_def) >>
     gvs[vyperTypeCallGraphTheory.int_calls_expr_def] >> metis_tac[]) >>
  irule attr_vv_sim >> metis_tac[]
QED

Theorem compile_attribute_case:
  !nocalls ctx func cenv cx ann obj fld.
    expr_vv_case nocalls ctx func cenv cx obj ==>
    expr_sim_case nocalls ctx func cenv cx (Attribute ann obj fld) /\
    expr_vv_case nocalls ctx func cenv cx (Attribute ann obj fld)
Proof
  rpt strip_tac >>
  `expr_vv_case nocalls ctx func cenv cx (Attribute ann obj fld)` by
    metis_tac[compile_attribute_vv_case] >>
  simp[] >> irule expr_sim_case_of_vv >> simp[]
QED

Theorem compile_attribute_vv_sim:
  !cenv obj.
    expr_vv_ok cenv obj ==>
    !ctx func cx env ty ann fld es.
      expr_sim_pre cenv cx env (Attribute ann obj fld) es ==>
      expr_vv_sim ctx func cenv cx ty (Attribute ann obj fld) es
Proof
  rw[expr_vv_ok_case] >>
  `expr_vv_case T ctx func cenv cx (Attribute ann obj fld)` by
    simp[compile_attribute_vv_case] >>
  gvs[expr_vv_case_def, expr_sim_pre_body] >> metis_tac[]
QED
