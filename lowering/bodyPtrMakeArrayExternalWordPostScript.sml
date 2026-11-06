(* Typed result boundary, separate from the raw counted load path. *)
Theory bodyPtrMakeArrayExternalWordPost
Ancestors
  bodyPtrMakeArrayCopyStep bodyPtrMakeArrayWordClean bodyPtrMakeArrayExternalFrame
  bodyPtrDefs exprSimUnwrapProps ptrDiscipline venomState venomInst context

Theorem external_word_load_ptr_val_ok:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  eval_operand src s = SOME a /\ is_word_type t /\
  (opc = SLOAD ==> key_taint tn.t_stor a = {}) /\
  (opc = TLOAD ==> key_taint tn.t_trans a = {}) ==>
  ptr_val_ok cx t v (Var tmp)
    (step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn)
    ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all external_load_output_ghost >> strip_tac >>
  simp[ptr_val_ok_def, op_prov_def] >> metis_tac[]
QED

Theorem storage_word_load_ptr_val_ok:
  ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s /\
  evaluate_type (get_tenv cx) t = SOME ty /\ is_word_type t /\
  eval_operand p.ptr_operand s = SOME a /\
  ((p.ptr_location = LocStorage /\ opc = SLOAD) \/
   (p.ptr_location = LocTransient /\ opc = TLOAD)) ==>
  ptr_val_ok cx t v (Var tmp)
    (step_prov PG G (mk_inst id opc [p.ptr_operand] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id opc [p.ptr_operand] [tmp]) s (update_var tmp w s) tn)
    ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all ptr_vv_word_key_clean >> strip_tac >>
  irule external_word_load_ptr_val_ok >> gvs[] >> qexists_tac `a` >> simp[]
QED

Theorem external_word_load_post:
  vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
  is_word_type (expr_type e) /\ sa.cs_next_var <= sm.cs_next_var /\
  stmt_state_rel ctx func cenv cx es'
    ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!ty. evaluate_type (get_tenv cx) (expr_type e) = SOME ty ==>
        w = typed_val_to_w256 ty v) /\
  (!x w'. not_fresh_at sm x /\ lookup_var x s = SOME w' ==>
    lookup_var x ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) = SOME w') /\
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\ eval_operand src s = SOME a /\
  (opc = SLOAD ==> key_taint tn.t_stor a = {}) /\
  (opc = TLOAD ==> key_taint tn.t_trans a = {}) /\
  type_memory_bytes cenv (lowered_value_type cenv e) = 0 /\
  ghost_inv d cenv cx es' G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==> x <> tmp) /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> tmp) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> tmp) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> tmp) ==>
  expr_post ctx func cenv cx e es sa sb s0 es' v (Var tmp)
    ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  ptr_val_ok cx (expr_type e) v (Var tmp)
    (step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn)
    ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  ptr_buf_ok cenv e (Var tmp)
    (step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s))
    ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  ghost_inv d cenv cx es'
    (step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn)
    ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  ghost_kept cenv es sa G0 tn0 s0
    (step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (irule expr_post_of_vv_post_load >>
      simp[eval_operand_def, lookup_var_def, update_var_def,
           finite_mapTheory.FLOOKUP_UPDATE] >>
      qexistsl_tac [`p`, `s`, `sm`, `t`] >>
      gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  conj_tac >- (irule external_word_load_ptr_val_ok >> metis_tac[]) >>
  conj_tac >- simp[ptr_buf_ok_def] >>
  conj_tac >- (irule external_load_ghost_inv >> metis_tac[]) >>
  irule external_load_ghost_kept >> metis_tac[]
QED
