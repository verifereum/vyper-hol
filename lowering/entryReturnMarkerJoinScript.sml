(* Code, resources, and first-exit transfer for the observed return stage. *)
Theory entryReturnMarkerJoin
Ancestors
  entryReturnMarkerResources entryReturnMarkerEdge entryReturnFirstExit
  entryReturnResourceTransport entryReturnDecodeLayout entryReturnDefaultLayout
  fragExec fragGasOriginPtr entryReturnMarker entryCreateFocusSpec
  createSizeCutRegion list venomInst rich_list
  compileEnv createSizeCutCode exprSimAbiGasBridge exprLoweringProps
  entryCreateIntervalLayout

Theorem extcall_return_marker_code:
  fn_has_code a b fn /\
  ~MEM b.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks a b)) ==>
  fn_has_code a b (return_marker_fn fn b.cs_current_bb (LENGTH b.cs_current_insts) id)
Proof
  simp[fn_has_code_def, return_marker_lookup] >> strip_tac >> conj_tac
  >- (gen_tac >> strip_tac >> rename1 `MEM c (emitted_blocks a b)` >>
      `c.bb_label <> b.cs_current_bb` by
        (qpat_x_assum `~MEM _ (MAP _ _)` mp_tac >> simp[MEM_MAP] >> metis_tac[]) >>
      simp[]) >>
  simp[] >> qpat_x_assum `_ ≼ _` (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  simp[IS_PREFIX_APPEND, TAKE_APPEND1]
QED

Theorem extcall_return_marker_agree:
  lookup_function fn.fn_name ctx.ctx_functions = SOME fn ==>
  return_resource_agree ctx fn (return_marker_ctx ctx fn label idx id)
    (return_marker_fn fn label idx id)
Proof
  strip_tac >>
  qspecl_then [`fn`,`label`,`idx`,`id`] mp_tac return_marker_insts_split >>
  strip_tac >>
  simp[return_resource_agree_def,return_marker_lookup_function,
       return_marker_resources,FILTER_APPEND]
QED

Theorem extcall_return_marker_path:
  create_cut_code {} a b /\ fn_has_code a b fn /\ no_phi_fn fn /\
  ALL_DISTINCT (fn_labels fn) /\
  ~MEM b.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks a b)) /\
  EVERY (\i. i.inst_opcode <> INVOKE) (frag_code a b) /\
  create_operand_at a s /\
  (case r of OK t => create_operand_at b t | _ => exit_result r) /\
  gas_origin_ptr_path
    (D,lo,E,return_marker_ctx ctx fn b.cs_current_bb (LENGTH b.cs_current_insts) id,
     return_marker_fn fn b.cs_current_bb (LENGTH b.cs_current_insts) id,PG)
    (s,G,tn) [] (r,G',tn') ==>
  gas_origin_ptr_path (D,lo,E,ctx,fn,PG) (s,G,tn) [] (r,G',tn') /\
  create_operand_full_scope a b E ctx fn s [] r
Proof
  strip_tac >>
  drule_all create_cut_region_rules >>
  disch_then (assume_tac o CONJUNCT1) >>
  irule return_empty_path_first_exit >>
  goal_assum (drule_at Any) >> simp[create_operand_at_def] >>
  (conj_tac >- fs[create_operand_at_def]) >>
  qexistsl_tac [`return_marker_ctx ctx fn b.cs_current_bb (LENGTH b.cs_current_insts) id`,
    `return_marker_fn fn b.cs_current_bb (LENGTH b.cs_current_insts) id`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      drule_at (Pat `gas_origin_ptr_edge _ _ _ _`) return_marker_edge_transfer >>
      simp[return_marker_resources] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  fs[fn_has_code_def, gas_origin_ptr_edge_def] >>
  metis_tac[return_marker_no_empty_edge, IS_PREFIX_LENGTH]
QED

Theorem extcall_return_layout:
  let rt = if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type;
      mn = abi_static_size cenv.ce_struct_fields rt;
      info = type_to_abi_dec_info cenv.ce_struct_fields cenv rt
  in
  (if ret_type = NoneT then comp_return (Lit 0w)
   else if has_default then
     comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
       (\r. compile_default_return_path cenv ret_type default_ty
         buf_op r.buf_operand default_op addr_op skip mn cap info)
   else comp_bind (compile_alloc_buffer (type_memory_bytes cenv ret_type))
     (\r. comp_bind (compile_return_value_decode mn cap)
       (\hi. comp_ignore_bind
         (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD buf_op hi info)
         (comp_return r.buf_operand)))) sr = (result_op,sb) /\
  (ret_type <> NoneT /\ has_default ==> create_layout sr sb) /\
  (ret_type <> NoneT /\ ~has_default ==>
    !suffix k. sr.cs_next_label <= k ==> sr.cs_current_bb <> fresh_label_output suffix k) ==>
  create_cut_code {} sr sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code sr sb) /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sr sb)) /\
  (sr.cs_current_bb = sb.cs_current_bb ==>
   LENGTH sr.cs_current_insts <= LENGTH sb.cs_current_insts)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >> Cases_on `ret_type = NoneT`
  >- (gvs[comp_return_def] >>
      simp[create_cut_code_empty,cs_extends_refl,frag_code_def,
           emitted_blocks_def,emitted_insts_def]) >>
  Cases_on `has_default` >> gvs[]
  >- (drule extcall_default_return_layout >> simp[]) >>
  qpat_x_assum `comp_bind _ _ sr = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule_all extcall_decode_return_layout >> simp[] >> strip_tac >> simp[] >>
  strip_tac >> Cases_on `emitted_blocks sr sb = []` >> fs[] >>
  fs[create_cut_code_def] >> drule frag_extends_emitted_shape >>
  simp[] >> strip_tac >> metis_tac[MEM_MAP, MEM_LAST_NOT_NIL]
QED
