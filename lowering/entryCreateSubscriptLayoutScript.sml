Theory entryCreateSubscriptLayout
Ancestors
  entryCreateEffectFocus entryCreateAdminSequence
  exprSimTuple exprSimMapKey exprSimPlaces exprSimSubscriptMap exprSimMapDefs
  exprLoweringProps emitHelperProps exprSimAbiGasBridge
  createSizeCutCode venomInst compileEnv fragExec list
  entryCreateFocusSpec abiEncoderProps venomExecSemantics venomState

(* The tuple index is a literal, and has no separate compiled interval. *)
Theorem create_subscript_tuple_layout:
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = TupleT tys /\ place_type ce obj = ValPT (TupleT tys) ==>
  expr_body_pre ce cx env obj es /\
  ?ity k bvv sm dst.
    idx = Literal ity (IntL (&k)) /\ k < LENGTH tys /\ EL k tys = ann /\
    compile_expr ce ty obj sa = (bvv,sm) /\
    emit_op ADD [vv_operand bvv; Lit (n2w (tuple_offset ce tys (vv_loc bvv)
                                      (literal_int_index idx)))] sm = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst (vv_loc bvv))
Proof
  strip_tac >> drule_all tuple_pre_base >> strip_tac >>
  drule_all compile_expr_tuple_subscript >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem create_subscript_tuple_suffix_code:
  emit_op ADD [baseop; Lit off] sm = (dst,sb) ==>
  create_cut_code {} sm sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code sm sb)
Proof
  strip_tac >> conj_tac
  >- (`create_cut_code {} sm (SND (emit_op ADD [baseop; Lit off] sm))` by
        simp[create_cut_code_emit_op, create_cut_targets_def] >>
      qpat_assum `emit_op _ _ _ = _` (fn th => fs[th])) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  fs[same_blocks_def, frag_code_def, emitted_blocks_def, mk_inst_def,
     DROP_LENGTH_NIL]
QED

(* Attach confinement at the state from the actual one-step selector run. *)
Theorem create_subscript_tuple_suffix_scope:
  emit_op ADD [baseop; Lit off] sm = (dst,sb) /\ fn_has_code sm sb f /\
  create_operand_at sm s /\ ~s.vs_halted /\ eval_operand baseop s = SOME w /\
  u = update_var (STRING #"%" (toString sm.cs_next_var)) (w + off) s ==>
  create_operand_full_scope sm sb E C f s []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by
    fs[create_operand_at_def] >>
  pop_assum (rewrite_tac o single o SYM) >>
  irule create_admin_sequence_scope >>
  fs[same_blocks_def, frag_ids_def, mk_inst_def, is_terminator_def,
     run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
     eval_operand_def]
QED

Theorem create_subscript_mapping_layout:
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  place_type ce obj = MapPT kt vt /\ expr_map_pre ce cx env obj es ==>
  ~copies_subscript_base ce obj idx /\ ~subscript_reads_base cx obj idx /\
  ?bvv sm key sn hashed sp slot.
    compile_expr ce ty obj sa = (bvv,sm) /\
    lower_value compile_expr ce (expr_type idx) idx sm = (key,sn) /\
    (if is_bytestring_type kt then compile_keccak256_key key F sn else (key,sn)) =
      (hashed,sp) /\
    compile_mapping_subscript (vv_operand bvv) hashed sp = (slot,sb) /\
    vv = LocatedValue ann (mk_ptr slot
      (case vv_location bvv of SOME l => l | NONE => LocMemory))
Proof
  strip_tac >>
  `?k v. type_place_expr env obj = SOME (HashMapT k v)` by
    fs[expr_map_pre_def] >>
  `~copies_subscript_base ce obj idx /\ ~subscript_reads_base cx obj idx` by
    metis_tac[map_base_no_overlap] >>
  drule_all compile_expr_mapping_subscript_parts >> simp[]
QED
