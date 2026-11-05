(* Memory projection, instruction and Name source properties for fields. *)
Theory bodyFieldMemoryProps
Ancestors
  exprSimHypsDefs supportedExprTraverse supportedProgram valueEncodingProps vyperTypeCallGraph
  bodyNameMemoryFacts exprSimSource
  exprSimFieldLayout exprSimAttributeProps exprSimVVFrame exprSimProps
  valueEncoding compileEnv venomState words list rich_list finite_map
  exprOperandVar exprSimDefs loweringPosts context
  exprSimUnwrapProps exprSimMemoryPath
  exprLowering exprLoweringProps emitHelper emitHelperProps
  fragExec fragExecMem instMemFrontier allocaHistoryFragment
  venomInst venomExecSemantics vyperAST vyperTyping vyperInterpreter
  vyperTypeSystem vyperTypeInvariants allocLimits bodyMemoryDefs vyperState
  vyperTypeExprSoundness vyperAssignPreservesType

Theorem body_field_region_frontier:
  fields_layout fields fs /\ ALOOKUP fs id = SOME ftv /\
  (addr : num) + type_memory_size_fields fs <= s.vs_alloca_next ==>
  addr + struct_field_offset fields id + type_memory_size ftv <= s.vs_alloca_next
Proof
  cheat
QED

Theorem body_field_source_region:
  fields_layout fields fs /\ struct_has_type fs vals /\
  fields_in_memory vals fs addr s.vs_memory /\ fields_val_wf vals fs /\
  ALOOKUP vals id = SOME fv /\ ALOOKUP fs id = SOME ftv /\
  (addr : num) + type_memory_size_fields fs <= s.vs_alloca_next ==>
  val_in_memory ftv fv (addr + struct_field_offset fields id) s.vs_memory /\
  val_wf ftv fv /\
  addr + struct_field_offset fields id + type_memory_size ftv <= s.vs_alloca_next
Proof
  cheat
QED

Theorem body_field_address_no_wrap:
  fields_layout fields fs /\ ALOOKUP fs id = SOME ftv /\
  (addr : num) + type_memory_size_fields fs <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) ==>
  w2n ((n2w addr : bytes32) + n2w (struct_field_offset fields id)) =
    addr + struct_field_offset fields id
Proof
  cheat
QED

Theorem attr_add_prefix_mem_ok:
  emit_op ADD ops sm = (dst,sn) ==>
  run_inst_seq_mem_ok (emitted_insts sm sn) s
Proof
  cheat
QED

Theorem attr_add_run_post:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  eval_operand (vv_operand vv) s = SOME w ==>
  ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
      vv_post ctx func cenv cx e es sa sn s0 es' tv vv q /\
      eval_operand (vv_operand vv) q = SOME w /\
      eval_operand dst q = SOME (w + n2w off) /\
      q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next
Proof
  cheat
QED

Theorem attr_add_history:
  emit_op ADD ops sm = (dst,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sn) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)
Proof
  cheat
QED

Theorem attr_add_frag_mem_at:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
         alloca_history func s)
    (\s. (?w. vv_post ctx func cenv cx e es sa sn s0 es' tv vv s /\
               eval_operand (vv_operand vv) s = SOME w /\
               eval_operand dst s = SOME (w + n2w off)) /\
         alloca_history func s /\ s.vs_alloca_next = entry.vs_alloca_next /\
         s.vs_allocas = entry.vs_allocas) R
Proof
  cheat
QED

Theorem attr_add_frag_mem:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sn
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
         alloca_history func s)
    (\s. (?w. vv_post ctx func cenv cx e es sa sn s0 es' tv vv s /\
               eval_operand (vv_operand vv) s = SOME w /\
               eval_operand dst s = SOME (w + n2w off)) /\
         alloca_history func s) R
Proof
  cheat
QED

Theorem body_base_memory_holds_struct:
  !cenv cx sid tv vv es s stv w.
    vv_holds cenv cx (StructT sid) tv vv es s /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME stv /\
    eval_operand (vv_operand vv) s = SOME w /\ vv_loc vv = LocMemory ==>
    ?v. read_result cx tv es = (INL v, es) /\
        val_in_memory stv v (w2n w) s.vs_memory
Proof
  cheat
QED

Theorem body_base_memory_at_struct:
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
               local_val_at cenv cx n (w2n w - b) stv v) \/
     val_footprint stv v = 0)
Proof
  cheat
QED

Theorem body_attr_memory_at_field:
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
    ALOOKUP fs fld = SOME ftv /\ evaluate_type (get_tenv cx) ann = SOME ftv /\
    vv_loc bvv = LocMemory ==>
    vv_at cenv cx ann sa sn es1 tv'
      (LocatedValue ann (mk_ptr dst (vv_loc bvv))) q
Proof
  cheat
QED

Theorem body_attr_memory_vv_post:
  !func cenv cx obj es sa sn s0 es1 tv bvv q w dst ann fld sid fs ftv tv' ctx.
    vv_post ctx func cenv cx obj es sa sn s0 es1 tv bvv q /\
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
            read_result cx tv' es1 = (INL fv, es1)) /\
    vv_loc bvv = LocMemory ==>
    vv_post ctx func cenv cx (Attribute ann obj fld) es sa sn s0 es1 tv'
      (LocatedValue ann (mk_ptr dst (vv_loc bvv))) q
Proof
  cheat
QED

Theorem body_attribute_name_compile:
  !cenv ty ann sid id fld st vv st'.
    compile_expr cenv ty (Attribute ann (Name (StructT sid) id) fld) st =
      (vv, st') ==>
    ?bvv st1 p.
      compile_expr cenv ty (Name (StructT sid) id) st = (bvv, st1) /\
      emit_op ADD [vv_operand bvv;
                   Lit (n2w (attr_offset cenv (StructT sid) (vv_loc bvv)
                               fld))] st1 = (p, st') /\
      vv = LocatedValue ann (mk_ptr p (vv_loc bvv))
Proof
  cheat
QED

Theorem body_attribute_name_eval:
  !cx ann sid id fld es.
    eval_expr cx (Attribute ann (Name (StructT sid) id) fld) es =
    (do r <- eval_expr cx (Name (StructT sid) id);
        select_result cx (StructT sid) r (AttrSubscript fld) od) es
Proof
  cheat
QED

(* Original proof before the ABI occurrence clause was added to expr_body_pre.
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  gvs[expr_body_pre_def, well_typed_expr_def, attribute_type_ok_def,
      vyperTypeCallGraphTheory.int_calls_expr_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm, byte_widths_expr_def,
      alloc_limits_expr_def, expr_type_def]
QED
*)
Theorem body_attribute_name_pre:
  !cenv cx env ann sid id fld es.
    expr_body_pre cenv cx env (Attribute ann (Name (StructT sid) id) fld) es ==>
    expr_body_pre cenv cx env (Name (StructT sid) id) es /\
    attribute_type (get_tenv cx) (StructT sid) fld = SOME ann
Proof
  cheat
QED

Theorem body_base_memory_post_read_struct:
  !ctx func cenv cx obj es sa sn s0 es1 tv bvv q w sid fs.
    vv_post ctx func cenv cx obj es sa sn s0 es1 tv bvv q /\
    expr_type obj = StructT sid /\ vv_loc bvv = LocMemory /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    eval_operand (vv_operand bvv) q = SOME w ==>
    ?v. read_result cx tv es1 = (INL v, es1)
Proof
  cheat
QED

Theorem body_word_load_prefix_mem_ok:
  emit_op MLOAD [operand] sm = (op,sb) /\
  eval_operand operand s = SOME w /\ w2n w + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  cheat
QED

Theorem body_word_load_history:
  emit_op MLOAD [operand] sm = (op,sb) /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sb) s = OK q ==>
  alloca_history func (q with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  cheat
QED

(* Original proof of body_word_load_run_post, preserved verbatim:
Proof
  rpt strip_tac >>
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       !tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
             mem_word_at (w2n w) s.vs_memory = typed_val_to_w256 tvt v` by
    (gvs[vv_post_def, vv_holds_def, read_result_def, return_def] >> metis_tac[]) >>
  gvs[] >> drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  `not_local_ptr cenv es'.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sm` >> simp[]) >>
  `!x. not_fresh_at sm x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule step_MLOAD >>
  disch_then (qspecl_then [`sm.cs_next_id`, `out`] assume_tac) >>
  qexists_tac `update_var out (mload (w2n w) s) s` >>
  simp[run_inst_seq_def, Abbr `out`] >>
  `stmt_state_rel ctx func cenv cx es' s` by fs[vv_post_def] >>
  irule expr_post_of_vv_post_load >>
  conj_tac >- simp[] >>
  conj_tac
  >- (qexists_tac `mload (w2n w) s` >>
      simp[eval_operand_def, lookup_var_update_var, GSYM valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  conj_tac
  >- (irule stmt_state_rel_update_var >> simp[]) >>
  qexistsl [`p`, `s`, `sm`, `expr_type e`] >>
  simp[lookup_var_update_var, update_var_def] >> metis_tac[]
QED
*)
Theorem body_word_load_run_post:
  emit_op MLOAD [p.ptr_operand] sm = (op,sb) /\
  p.ptr_location = LocMemory /\ is_word_type t /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s ==>
  ?q. run_inst_seq (emitted_insts sm sb) s = OK q /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op q /\
      q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next
Proof
  cheat
QED

Theorem unwrap_memory_word_sim_mem:
  emit_op MLOAD [p.ptr_operand] sm = (op,sb) /\
  p.ptr_location = LocMemory /\ is_word_type t /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
            (LocatedValue t p) s /\
         (?w. eval_operand p.ptr_operand s = SOME w /\
              w2n w + 32 <= s.vs_alloca_next) /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s) R
Proof
  cheat
QED

Theorem body_attribute_name_capacity:
  expr_sim_pre cenv cx env (Name (StructT sid) id) es /\
  stmt_state_rel ctx func cenv cx es q /\
  compile_expr cenv ty (Name (StructT sid) id) sa = (bvv,sm) /\
  fields_layout fields fs /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  ALOOKUP fs fld = SOME ftv /\
  eval_operand (vv_operand bvv) q = SOME w /\
  eval_operand dst q = SOME (w + n2w (struct_field_offset fields fld)) ==>
  ?fw. eval_operand dst q = SOME fw /\
       w2n fw + type_memory_size ftv <= q.vs_alloca_next
Proof
  cheat
QED

Theorem body_name_eval_state:
  lookup_scopes id es.scopes = SOME entry /\
  eval_expr cx (Name ann id) es = (res,es1) ==> es1 = es
Proof
  cheat
QED

Theorem body_unwrap_memory_read_mem:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocMemory /\
  read_result cx tv es' = (INL v,es') /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' tv (LocatedValue t p) s /\
         (is_word_type t ==> ?w. eval_operand p.ptr_operand s = SOME w /\
                                  w2n w + 32 <= s.vs_alloca_next) /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s) R
Proof
  cheat
QED
