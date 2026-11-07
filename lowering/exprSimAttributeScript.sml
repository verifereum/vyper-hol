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
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv context
  accountsRelProps
  valueEncoding vyperAST vyperInterpreter vyperState vyperStorage vyperValue
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
  cheat
QED

Theorem eval_expr_attribute:
  !cx ann obj fld es.
    eval_expr cx (Attribute ann obj fld) es =
    (do r <- eval_expr cx obj;
        select_result cx (expr_type obj) r (AttrSubscript fld) od) es
Proof
  cheat
QED

Theorem attr_pre_base:
  !cenv cx env ann obj fld es.
    expr_body_pre cenv cx env (Attribute ann obj fld) es ==>
    expr_body_pre cenv cx env obj es /\
    ?sid. expr_type obj = StructT sid /\
          attribute_type (get_tenv cx) (StructT sid) fld = SOME ann
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem attr_extends:
  !ops sa p sb. emit_op ADD ops sa = (p, sb) ==> cs_extends sa sb
Proof
  cheat
QED

(* ===== The value_vv of the field ===== *)



Theorem struct_value_shape:
  !fs v. value_has_type (StructTV fs) v ==>
         ?vals. v = StructV vals /\ struct_has_type fs vals
Proof
  cheat
QED

Theorem immutable_holds_read:
  !cenv cx t tv w es s.
    immutable_holds cenv cx t tv w es s ==> ?v. read_result cx tv es = (INL v, es)
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

(* A struct's field sits inside the struct's layout at the field's offset. *)
Theorem sub_layout_field[local]:
  !itv iv k fs vals fields fld ftv fv.
    sub_layout itv iv k (StructTV fs) (StructV vals) /\
    fields_layout fields fs /\ struct_has_type fs vals /\
    ALOOKUP vals fld = SOME fv /\ ALOOKUP fs fld = SOME ftv ==>
    sub_layout itv iv (k + struct_field_offset fields fld) ftv fv
Proof
  cheat
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
  cheat
QED

Theorem type_widens_to_struct[local]:
  type_widens_to tenv t (StructT sid) ==> t = StructT sid
Proof
  cheat
QED

Theorem attr_post_value_type:
  expr_body_pre cenv cx env obj es /\ expr_type obj = StructT sid ==>
  post_value_type cenv obj = expr_type obj
Proof
  cheat
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
  cheat
QED

(* ===== The simulation ===== *)

Theorem attr_eval_inst_idx[local]:
  !op s n. eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  cheat
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
  cheat
QED

Theorem attr_source[local]:
  !cx ann obj fld.
    eval_expr cx (Attribute ann obj fld) =
    bind (eval_expr cx obj)
      (\r. select_result cx (expr_type obj) r (AttrSubscript fld))
Proof
  cheat
QED

(* The field's selection reads no gas observation. *)
Theorem attr_select_gas_obs[local]:
  !cx ty tv fld ee r.
    select_result cx ty tv (AttrSubscript fld) ee = (r, ee) ==>
    !tail. select_result cx ty tv (AttrSubscript fld)
             (ee with gas_obs := tail) = (r, ee with gas_obs := tail)
Proof
  cheat
QED

Theorem attr_operand_admissible[local]:
  !cenv cx env e es.
    expr_body_pre cenv cx env e es ==>
    gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  cheat
QED

Theorem attr_exempt_cert[local]:
  !memory tops p cx ann obj fld start marks out endpoint.
    gas_exempt_cert memory tops p (ignore_bind (eval_expr cx obj) (return ()))
      start marks out endpoint ==>
    gas_exempt_cert memory tops p
      (ignore_bind (eval_expr cx (Attribute ann obj fld)) (return ()))
      start marks out endpoint
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem attr_vv_sim[local]:
  !ctx func cenv cx env ty ann obj fld es sid.
    expr_body_pre cenv cx env (Attribute ann obj fld) es /\
    expr_body_pre cenv cx env obj es /\ expr_type obj = StructT sid /\
    attribute_type (get_tenv cx) (StructT sid) fld = SOME ann /\
    expr_vv_sim ctx func cenv cx ty obj es ==>
    expr_vv_sim ctx func cenv cx ty (Attribute ann obj fld) es
Proof
  cheat
QED

Theorem compile_attribute_vv_case:
  !nocalls ctx func cenv cx ann obj fld.
    expr_vv_case nocalls ctx func cenv cx obj ==>
    expr_vv_case nocalls ctx func cenv cx (Attribute ann obj fld)
Proof
  cheat
QED

Theorem compile_attribute_case:
  !nocalls ctx func cenv cx ann obj fld.
    expr_vv_case nocalls ctx func cenv cx obj ==>
    expr_sim_case nocalls ctx func cenv cx (Attribute ann obj fld) /\
    expr_vv_case nocalls ctx func cenv cx (Attribute ann obj fld)
Proof
  cheat
QED

Theorem compile_attribute_vv_sim:
  !cenv obj.
    expr_vv_ok cenv obj ==>
    !ctx func cx env ty ann fld es.
      expr_sim_pre cenv cx env (Attribute ann obj fld) es ==>
      expr_vv_sim ctx func cenv cx ty (Attribute ann obj fld) es
Proof
  cheat
QED
