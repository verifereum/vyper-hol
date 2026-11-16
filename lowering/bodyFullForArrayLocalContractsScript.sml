(* Interface-only diagnostic.  The ML terms below are NOT HOL definitions,
   axioms, suppliers or theorem assumptions.  In particular parsing them does
   not certify caller applicability.  The candidate is deliberately retained
   literally so that a failed premise cannot be silently hidden. *)
Theory bodyFullForArrayLocalContracts
Ancestors
  bodyFullPreds bodyFullGhostFrame bodyPtrDefs exprSimHypsDefs loweringPosts
  stmtLowering compileEnv codegenRel contextCodegenRel fragExec
  fragGasOriginPtrLoop ptrDiscipline venomInst venomState
  vyperInterpreter vyperTypeSystem vyperState vyperTyping vyperValue
  supportedStmts supportedStmtTraverse valueEncoding exprSimAggregateLayout
  finite_map list words stmtSimForArrayLoop

val _ = Parse.hide "body";

val local_round_entry_candidate = ``
  body_inv tops ctx cenv cx /\
  supported_stmts tops bindings stmts /\
  aty = ArrayT typ bd /\
  id NOTIN FDOM env.var_types /\
  FLOOKUP env.var_types name = SOME (ArrayT typ bd) /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ap) az) /\
  saved_base = Var ap /\
  type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
  call_evaluation_safe cx (int_calls_stmts stmts) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  declare_local cenv id typ sdecl = (bc,sdecl') /\ same_frame cenv bc /\
  cenv_top_ext cenv bc (FEMPTY :: ee.scopes) /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_scopes id ee.scopes = NONE /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved bc scopy /\
  ret_pc_ok cenv sa s0 /\ copy_old_operand scopy bound_op /\
  copy_old_operand sa saved_base /\
  ~ctx_has_dalloca ctx /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> x <> idx /\ x <> dv /\ x <> ov /\ x <> ep) /\
  not_fresh_at scopy idx /\ not_fresh_at scopy p /\ not_fresh_at scopy ep /\
  p <> ov /\ p <> ep /\
  not_local_ptr cenv ee.scopes ov /\ not_local_ptr cenv ee.scopes ep /\
  ALL_DISTINCT [idx;dv;ov;ep;p] /\
  (bd = Dynamic (bound_length bd) ==> ALL_DISTINCT [idx;dv;ov;tov;ep;p]) /\
  (!x. bound_op = Var x ==> x <> dv /\ x <> ov /\ x <> tov /\
    x <> ep /\ x <> idx /\ x <> nv) /\
  (!x. saved_base = Var x ==> x <> dv /\ x <> ov /\ x <> tov /\ x <> ep) /\
  fn_inst_ids_distinct func /\ MEM ainst (fn_insts func) /\
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  lookup_block cond_lbl func.fn_blocks = SOME
    <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var idx;bound_op] [dv];
       mk_inst j2 JNZ [Var dv;Label exit_lbl;Label body_lbl] []]|> /\
  lookup_block body_lbl func.fn_blocks = SOME
    <|bb_label := body_lbl; bb_instructions := sb0.cs_current_insts ++ tail_code|> /\
  scopy.cs_current_bb = body_lbl /\
  scopy.cs_current_insts =
    [mk_inst j3 MUL [Var idx;Lit (n2w bytes)] [ov]] ++
    (case bd of Fixed n => []
     | Dynamic n => [mk_inst joff ADD [Lit 32w;Var ov] [tov]]) ++
    [mk_inst j4 ADD [saved_base;
      (case bd of Fixed n => Var ov | Dynamic n => Var tov)] [ep]] /\
  (bd = Dynamic (bound_length bd) ==>
    not_fresh_at scopy tov /\ tov <> p /\ tov <> idx /\
    (!x. not_fresh_at sa x ==> x <> tov) /\
    (joff <> j3 /\ joff <> j4)) /\
  compile_iter_elem_copy cenv (Var ep) (Var p) bytes LocMemory F typ typ
    scopy = ((),sb0) /\ fn_has_code scopy sb0 func /\
  cs_extends scopy sb0 /\ scopy.cs_next_var <= sb0.cs_next_var /\
  bytes = type_memory_size tv /\ type_memory_bytes cenv typ = bytes /\
  0 < bytes /\ bytes + 64 < dimword (:256) /\
  extent = (if bytes <= 32 then 32 else 32*((bytes+31) DIV 32)) /\
  sz = type_memory_bytes cenv typ /\ extent <= sz /\
  sa.cs_next_var <= scopy.cs_next_var /\
  sa.cs_next_var <= sb0.cs_next_var /\ cs_extends sa sb0 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  k < LENGTH vs /\ MAP Value (DROP k vs) = Value v :: rs /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_sim_inv cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    dead_lo_ok H (DF H) lo cenv cx /\
    return_buf_frame d cenv sa s /\ alloca_history func s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ allocas_from lo s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ~s.vs_halted /\ s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
    LENGTH vs < dimword (:256) /\ lookup_var idx s = SOME (n2w k) /\
    eval_operand bound_op s = SOME (n2w (LENGTH vs)) /\
    FLOOKUP G idx = NONE /\ op_prov G bound_op = NONE /\
    op_taint tn (Var idx) = {} /\ op_taint tn bound_op = {} /\
    lookup_scopes name ee.scopes = SOME ent /\
    ent.type = ArrayTV tv bd /\ ent.value = ArrayV av /\
    vs = array_elements ent.type av /\
    eval_operand saved_base s = SOME arr_base /\
    lookup_var p s = SOME dst /\ ptr_covers G tn p s sz /\
    FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    w2n dst + sz < dimword (:256) /\ w2n dst + sz <= s.vs_alloca_next /\
    (!nm b len. local_region cenv ee.scopes s nm b len ==>
      regions_disjoint (w2n dst) sz b len) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x s = SOME w) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP s.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))) ==>
  ?ss Gs ts. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK ss,Gs,ts) /\
    expr_sim_inv bc cx (extend_local env id typ F)
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) :: ee.scopes;
        gas_obs := []|>) /\
    stmt_state_rel H ctx func bc cx
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) :: ee.scopes;
        gas_obs := []|>) ss /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d bc sb0 ss /\ alloca_history func ss /\
    ghost_inv_at (DF H) lo d bc cx
      (ee with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) :: ee.scopes;
        gas_obs := []|>) Gs ts ss /\
    ~ss.vs_halted /\ ss.vs_current_bb = sb0.cs_current_bb /\
    ss.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ret_pc_ok bc sb0 ss /\
    allocas_from lo ss /\ s0.vs_alloca_next <= ss.vs_alloca_next /\
    lookup_var p ss = SOME dst /\ ptr_covers Gs ts p ss sz /\
    FLOOKUP ss.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    w2n dst + sz < dimword (:256) /\ w2n dst + sz <= ss.vs_alloca_next /\
    (!nm b len. local_region cenv ee.scopes ss nm b len ==>
      regions_disjoint (w2n dst) sz b len) /\
    lookup_var idx ss = SOME (n2w k) /\
    eval_operand bound_op ss = SOME (n2w (LENGTH vs)) /\
    FLOOKUP Gs idx = NONE /\ op_prov Gs bound_op = NONE /\
    op_taint ts (Var idx) = {} /\ op_taint ts bound_op = {} /\
    lookup_scopes name ee.scopes = SOME ent /\
    ent.type = ArrayTV tv bd /\ ent.value = ArrayV av /\
    vs = array_elements ent.type av /\
    eval_operand saved_base ss = SOME arr_base /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x ss = SOME w) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP ss.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gs x = FLOOKUP G0 x /\
      op_taint ts (Var x) = op_taint tn0 (Var x))``;

(* Premise-to-caller audit, receiver source locations:
   - Local type/base: bodyMemForArray fixed source facts; dynamic prefix's
     lookup packet.  PtrVar source has provenance: no NONE premise is valid.
   - Address/copy syntax: stmtLowering 1293-1363.  Name returns LocMemory;
     MUL stride is type_memory_bytes; only Dynamic emits the header ADD.
   - Destination size/declaration: declare_local_def; sz=bytes, not a rounded
     independent allocation.  Alignment follows type_memory_size_aligned.
   - POSITIVITY IS NOT YET CERTIFIED. supported_iterator's Name branches
     require only matching element types and a bound. supported_type_namespace
     accepts empty tuples, zero fixed arrays and NoneT.  Source evaluation and
     well_formed_type_value must be checked as well; a 0-byte element would
     make both 0<bytes and extent<=sz fail.  This is local interface uncertainty,
     not an absent upstream supplier premise or a frozen-theorem falsehood.
   - Source coverage/robustness: local_ptrs_rel from stmt_state_rel supplies
     memory_value_rel and allocation capacity; ghost_inv_at supplies ptr_covers
     and robust val_in_memory under mem_agree_outside.  Header version is
     bodyFullForArrayDynamicStart.for_array_dynamic_header_full, lines 74-92.
   - Source snapshot after body: iterator_unmodified plus source preservation;
     lookup packet is NOT derivable merely from expr_sim_inv (values may vary).
   - Dynamic freshness is guarded for tov/joff, but the retained bound_op and
     saved_base clauses also mention tov unconditionally. Fixed compilation
     emits no tov; a caller can choose an unused witness but may not infer an
     emitted variable or demand its not_fresh_at property.
   - Callback exit/scopes: must use C1.5.1's full eliminator and C1.5.2's actual
     popped-state transport. No pointer-only normalized post is sufficient.
   - Fixed entry supplies condition endpoint/source snapshot and ghost frame;
     dynamic prefix supplies header + allocated endpoint, followed by exact
     dynamic entry path.  These are not completed body-round certificates.
*)

Theorem local_round_zero_tuple_diagnostic:
  supported_stmt [] []
    (For "x" (TupleT [])
      (Array (Name (ArrayT (TupleT []) (Fixed 1)) "a")) 1 []) /\
  evaluate_type tenv (TupleT []) = SOME (TupleTV []) /\
  well_formed_type_value (TupleTV []) /\
  type_memory_bytes cenv (TupleT []) = 0 /\
  type_memory_size (TupleTV []) = 0 /\
  ~((0:num) < 0) /\
  ~((if (0:num) <= 32 then 32 else 32*((0+31) DIV 32)) <= 0)
Proof
  simp[supported_stmt_def,supported_iterator_def,supported_type_namespace_def,
    supported_stmt_expr_exists_def,
    evaluate_type_def,well_formed_type_value_def,type_slot_size_def,
    type_memory_bytes_def,type_memory_size_def]
QED

(* REJECTED: local_round_entry_candidate above is not for caller use.
   Revise only the explicitly rejected size/fixed-temporary conjuncts.  This
   is syntax construction on quoted terms, never a rewrite of a HOL theorem.
   Expose the changed clauses literally, preserving all other conjunct order. *)
val (local_entry_old_pre, local_entry_post) =
  boolSyntax.dest_imp local_round_entry_candidate;
val local_entry_drop = [``0 < (bytes:num)``,
  ``extent = (if bytes <= 32 then 32 else 32*((bytes+31) DIV 32))``,
  ``(extent:num) <= sz``];
val local_entry_replacements =
  [(``!x. bound_op = Var x ==> x <> dv /\ x <> ov /\ x <> tov /\
          x <> ep /\ x <> idx /\ x <> nv``,
    ``!x. bound_op = Var x ==> x <> dv /\ x <> ov /\
          (bd = Dynamic (bound_length bd) ==> x <> tov) /\
          x <> ep /\ x <> idx /\ x <> nv``),
   (``!x. saved_base = Var x ==> x <> dv /\ x <> ov /\ x <> tov /\ x <> ep``,
    ``!x. saved_base = Var x ==> x <> dv /\ x <> ov /\
          (bd = Dynamic (bound_length bd) ==> x <> tov) /\ x <> ep``)];
fun local_entry_clause tm =
  case List.find (fn (old,_) => aconv old tm) local_entry_replacements of
    NONE => tm | SOME (_,replacement) => replacement;
val local_entry_retained =
  List.filter (fn tm => not (List.exists (fn bad => aconv bad tm) local_entry_drop))
    (boolSyntax.strip_conj local_entry_old_pre);
val local_round_entry_revised = boolSyntax.mk_imp
  (boolSyntax.list_mk_conj (map local_entry_clause local_entry_retained),
   local_entry_post);
(* Fail at typechecking time if a literal transformation did not apply. *)
val _ = if length (boolSyntax.strip_conj local_entry_old_pre) =
             length local_entry_retained + 3 andalso
           List.all (fn (old,_) => List.exists (aconv old) local_entry_retained)
             local_entry_replacements andalso
           not (List.exists (fn v => term_to_string v = "extent")
             (free_vars local_round_entry_revised))
        then () else raise Fail "local entry clause transformation mismatch";

Theorem local_round_zero_copy:
  ~is_word_type typ /\ ~is_bytestring_type typ /\
  type_memory_bytes cenv typ = 0 ==>
  compile_iter_elem_copy cenv src dst 0 LocMemory F typ typ s = ((),s)
Proof
  simp[compile_iter_elem_copy_def,contextTheory.compile_store_memory_def,
    contextTheory.compile_copy_memory_def,comp_return_def]
QED

(* Unchanged provider contracts quoted as data; no dependency on their proof
   theories (in particular the unfinished dynamic prefix) is introduced. *)
val fixed_entry_contract = ``
  compile_alloc_buffer sz sa = (buf,sb) /\ buf.buf_operand = Var p /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  lookup_block sb.cs_current_bb func.fn_blocks = SOME
    <|bb_label := sb.cs_current_bb; bb_instructions :=
      sb.cs_current_insts ++ [mk_inst aj JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks = SOME
    <|bb_label := entry; bb_instructions :=
      [mk_inst ei ASSIGN [Lit 0w] [idx]; mk_inst ej JMP [Label cond] []]|> /\
  sz < dimword (:256) /\ LENGTH vs < dimword (:256) /\
  p <> idx /\ (!x. not_fresh_at sa x ==> x <> idx) /\
  local_ptrs_reserved cenv sa /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x. saved_base = Var x ==> not_fresh_at sa x) /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes name es.scopes = SOME ent /\
  ent.type = ArrayTV tv (Fixed (LENGTH vs)) /\ ent.value = ArrayV av /\
  vs = array_elements ent.type av /\
  eval_operand saved_base s0 = SOME array_base /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~ctx_has_dalloca ctx /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?dst cc Gentry tnentry.
    lookup_var p cc = SOME dst /\ ptr_covers Gentry tnentry p cc sz /\
    FLOOKUP cc.vs_allocas sa.cs_next_id = SOME (w2n dst,sz) /\
    w2n dst + sz < dimword (:256) /\ w2n dst + sz <= cc.vs_alloca_next /\
    (!nm b len. local_region cenv es.scopes cc nm b len ==>
      regions_disjoint (w2n dst) sz b len) /\
    ~cc.vs_halted /\ cc.vs_current_bb = cond /\ cc.vs_inst_idx = 0 /\
    lookup_var idx cc = SOME 0w /\ FLOOKUP Gentry idx = NONE /\
    op_taint tnentry (Var idx) = {} /\
    lookup_scopes name es.scopes = SOME ent /\
    ent.type = ArrayTV tv (Fixed (LENGTH vs)) /\ ent.value = ArrayV av /\
    vs = array_elements ent.type av /\
    eval_operand saved_base cc = SOME array_base /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      expr_sim_inv cenv cx env es /\ stmt_state_rel H ctx func cenv cx es cc /\
      storage_well_formed_on cx es (FST H) /\
      return_buf_frame d cenv sa cc /\ alloca_history func cc /\
      s0.vs_alloca_next <= cc.vs_alloca_next /\ allocas_from lo cc /\
      ghost_inv_at (DF H) lo d cenv cx es Gentry tnentry cc) /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x cc = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
      FLOOKUP cc.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gentry x = FLOOKUP G0 x /\
      op_taint tnentry (Var x) = op_taint tn0 (Var x)) /\
    (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) []
      (OK cc,Gentry,tnentry))``;

val dynamic_prefix_contract = ``
  emit_op MLOAD [Var ap] st = (Var lv,sa) /\
  compile_alloc_buffer sz sa = (buf,sb) /\ buf.buf_operand = Var p /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  lookup_block sb.cs_current_bb func.fn_blocks = SOME
    <|bb_label := sb.cs_current_bb; bb_instructions :=
      sb.cs_current_insts ++ [mk_inst aj JMP [Label entry] []]|> /\
  sz < dimword (:256) /\ c < dimword (:256) /\
  local_ptrs_reserved cenv st /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes name es.scopes = SOME ent /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ap) az) /\
  ent.type = ArrayTV tv (Dynamic c) /\ ent.value = ArrayV av /\
  vs = array_elements ent.type av /\ LENGTH vs <= c /\
  return_buf_frame d cenv st s /\ alloca_history func s /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?dst t Gp tp.
    lookup_var lv t = SOME (n2w (LENGTH vs)) /\
    FLOOKUP Gp lv = NONE /\ op_taint tp (Var lv) = {} /\
    lookup_var p t = SOME dst /\ ptr_covers Gp tp p t sz /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n dst,sz) /\
    w2n dst + sz < dimword (:256) /\ w2n dst + sz <= t.vs_alloca_next /\
    (!nm b len. local_region cenv es.scopes t nm b len ==>
      regions_disjoint (w2n dst) sz b len) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    return_buf_frame d cenv sb t /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es t /\
      storage_well_formed_on cx es (FST H) /\ allocas_from lo t /\
      ghost_inv_at (DF H) lo d cenv cx es Gp tp t) /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gp x = FLOOKUP G x /\ op_taint tp (Var x) = op_taint tn (Var x)) /\
    (!aid bl. FLOOKUP s.vs_allocas aid = SOME bl ==>
      FLOOKUP t.vs_allocas aid = SOME bl) /\
    (?base. lookup_var ap s = SOME base /\
      mload (w2n base) s = n2w (LENGTH vs) /\
      ptr_covers G tn ap s 32 /\ mem_word_taint tn.t_mem (w2n base) = {}) /\
    exec_alloca (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p])
      ((update_var lv (n2w (LENGTH vs)) s) with
        vs_inst_idx := LENGTH sa.cs_current_insts) (n2w sz : bytes32) =
      OK (t with vs_inst_idx := LENGTH sa.cs_current_insts) /\
    (!D. inst_seq_ptr D lo ctx func PG G tn
      [mk_inst st.cs_next_id MLOAD [Var ap] [lv];
       mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]] s Gp tp) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gp,tp))``;

val dynamic_entry_contract = ``
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [mk_inst mi MLOAD [saved_base] [lv]; ainst;
              mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx];
       mk_inst e2 GT [Var lv; Lit (n2w c)] [g];
       mk_inst e3 ISZERO [Var g] [vld];
       mk_inst e4 ASSERT [Var vld] [];
       mk_inst e5 JMP [Label cond] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\ P es /\
  lookup_scopes id es.scopes = NONE /\
  eval_operand saved_base s0 = SOME array_base /\
  mload (w2n array_base) s0 = n2w (LENGTH vs) /\
  LENGTH vs <= c /\ c < dimword (:256) /\ ret_pc_ok cenv st s0 /\
  ALL_DISTINCT [lv;p;idx;g;vld] /\
  not_local_ptr cenv es.scopes lv /\ not_local_ptr cenv es.scopes p /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes g /\
  not_local_ptr cenv es.scopes vld /\
  (!x. saved_base = Var x ==> ~MEM x [lv;p;idx;g;vld]) /\
  (!x. not_fresh_at st x ==> ~MEM x [lv;p;idx;g;vld]) /\
  alloca_history func s0 /\ w2n array_base + 32 <= s0.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s0 /\ lo <= s0.vs_alloca_next /\
  exec_alloca ainst (update_var lv (n2w (LENGTH vs)) s0)
    (n2w sz : bytes32) = OK sA /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G tn
    [mk_inst mi MLOAD [saved_base] [lv];ainst] s0 G1 tn1) /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G1 tn1
    [mk_inst e1 ASSIGN [Lit 0w] [idx];
     mk_inst e2 GT [Var lv;Lit (n2w c)] [g];
     mk_inst e3 ISZERO [Var g] [vld];
     mk_inst e4 ASSERT [Var vld] []] (jump_to entry sA) G2 tn2) ==>
  ?dst cc s1.
    exec_alloca ainst (update_var lv (n2w (LENGTH vs)) s0)
      (n2w sz : bytes32) = OK s1 /\ s1 = sA /\
    cc = jump_to cond (update_var vld 1w (update_var g 0w
      (update_var idx 0w (jump_to entry s1)))) /\
    array_loop_inv ctx func cenv cx st0 P vs id idx saved_base array_base p dst sz
      ainst cond st 0 es cc /\
    lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame st s0 cc /\
    gas_marked_path F ctx func s0 0 (OK cc) /\
    gas_path_mem ctx func s0 0 (OK cc) /\
    alloca_history func cc /\ cc.vs_memory = s0.vs_memory /\
    s0.vs_alloca_next <= cc.vs_alloca_next /\
    (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s0,G,tn) [] (OK cc,G2,tn2))``;

(* C1.5.1 callback: literal RangeBody contract minus ONLY size=32. *)
val local_body_fragment_contract = ``
  !cx id typ it n stmts tops bindings ctx shadow_ctx func shadow_func
    cenv bc env env' ret_ty RetQ ee DF lo d PG st st1.
  body_stmts_full_ok cx stmts /\
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (For id typ it n stmts) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ it n stmts) ==> occurs_abi_decode_target target tops) /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ it n stmts) = SOME env' /\
  stmt_exprs_ok cenv (For id typ it n stmts) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ it n stmts)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty /\
  declare_local cenv id typ st = (bc,st1) /\ same_frame cenv bc /\
  expr_sim_inv bc cx (extend_local env id typ F) ee ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty stmts)
    (stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty (MAP gas_shadow_stmt stmts))
    (eval_stmts cx stmts) ee``;

(* Literal delivered C1.5.1 eliminator, up to consistent variable renaming.
   Its source parameter stays general; callers specialize to eval_stmts. *)
val local_body_outcome_contract = ``
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ bc (stmts_env bc lctx ret_ty stmts)
    (stmts_env bc lctx ret_ty (MAP gas_shadow_stmt stmts)) source ee /\
  stmts_env bc lctx ret_ty stmts sa = (cenv',sb) /\
  stmts_env bc lctx ret_ty (MAP gas_shadow_stmt stmts) shadow_sa =
    (cenv',shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  (!H. dead_lo_ok H (DF H) lo bc cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved bc sa /\
  ret_pc_ok bc sa s0 /\
  (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\
  gas_admissible source (stmt_res_ok lctx) ee /\
  return_buf_frame d bc sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_no_wrap inst s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func bc cx ee s0 /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d bc cx ee G0 tn0 s0) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 source (ee,s0,G0,tn0)
    (\H res mid G tn t. mid.gas_obs = [] /\ ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext bc cenv'' mid.scopes /\
      stmt_state_rel H ctx func cenv'' cx mid t /\
      storage_well_formed_on cx mid (FST H) /\
      return_buf_frame d cenv'' sb t /\ alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx mid G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)))
    (\H res mid gt r.
      (!tail. stmt_exit_ptr (RetQ H) (mid with gas_obs := tail) res gt r) /\
      halt_exit H cx mid res r /\
      (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))``;

(* C1.5.2 rich handler, not the lossy pointer-only theorem. *)
val local_handled_round_contract = ``
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmts cx body)
    (((es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv;
                          value := v; popped := []|>)) :: es.scopes)
       with gas_obs := []),s,G,tn)
    B (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
        !u. (r = Halt u \/ ?ir. r = IntRet ir u) ==> allocas_below_fmp u)) /\
  ~s.vs_halted /\
  (!res ee G1 tn1 t gs.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      B H res ee G1 tn1 t) /\
    eval_stmts cx body
      ((es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv;
                          value := v; popped := []|>)) :: es.scopes)
       with gas_obs := gs) = (res,ee) ==>
    (res = INL () \/ res = INR BreakException \/
     res = INR ContinueException) /\
    ?u G2 tn2. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (t,G1,tn1) [] (OK u,G2,tn2) /\
      Q H (INL (res = INR BreakException))
        (ee with scopes := TL ee.scopes) G2 tn2 u) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (do push_scope_with_var id tv v;
        finally (try (do eval_stmts cx body; return F od)
                     handle_loop_exception) pop_scope od)
    (es,s,G,tn) Q
    (\H res ee gt r. ?ex. res = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ee (INR ex) r /\
      (ctx_has_dalloca ctx ==>
        !u. (r = Halt u \/ ?ir. r = IntRet ir u) ==> allocas_below_fmp u))``;

(* Literal frozen root. Restriction is added below, not to this source term. *)
val frozen_for_fragment = ``
  !cx id typ it n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx it) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (For id typ it n body)))
      (eval_stmt cx (For id typ it n body)) es``;

(* Universal closure is syntax only. No kernel theorem is manufactured. *)
fun close_contract tm = boolSyntax.list_mk_forall (free_vars tm,tm);
val local_array_restriction = ``it = Array (Name (ArrayT typ bd) name)``;
val (for_variables, for_implication) = boolSyntax.strip_forall frozen_for_fragment;
val (for_pre, for_post) = boolSyntax.dest_imp for_implication;
val restricted_for_fragment = close_contract (boolSyntax.list_mk_forall
  (for_variables, boolSyntax.mk_imp
    (boolSyntax.mk_conj (local_array_restriction,for_pre),for_post)));
val entry_provider_contracts = map close_contract
  [fixed_entry_contract,dynamic_prefix_contract,dynamic_entry_contract];
val private_helper_contracts = map close_contract
  [local_body_fragment_contract,local_body_outcome_contract,
   local_handled_round_contract,local_round_entry_revised];
(* Final interface: ONLY unchanged entry providers. Internal interface: PROPOSED,
   pending caller audit/approval, not an authorized shared supplier statement. *)
val final_local_consumer_contract = boolSyntax.mk_imp
  (boolSyntax.list_mk_conj entry_provider_contracts,restricted_for_fragment);
val proposed_internal_local_consumer_contract = boolSyntax.mk_imp
  (boolSyntax.list_mk_conj (entry_provider_contracts @ private_helper_contracts),
   restricted_for_fragment);
val _ = if null (free_vars final_local_consumer_contract) andalso
           null (free_vars proposed_internal_local_consumer_contract)
        then () else raise Fail "unclosed local consumer contract";

(* Corrected branch-sensitive caller audit (supersedes the REJECTED map's
   positivity/extent clauses, not the frozen root or any provider statement).

   SYNTAX AND CLOSED INTERFACES
   fixed_entry_contract: bodyFullForArrayFixedStart:86-140, unchanged.
   dynamic_prefix_contract: bodyFullForArrayDynamicStart:164-221, unchanged.
   dynamic_entry_contract: bodyFullForArrayInit:10-65, unchanged.
   The three source texts were compared clause-by-clause; their witnesses
   remain outside all valid-H conclusions. Closure binds their free variables,
   not their existential endpoints. The two private body contracts are
   RangeBody:64-85 minus size=32, and bodySimFull:198-254 specialized to stmts
   and bc (source kept general as in the delivered eliminator), with ONLY
   mid.gas_obs=[] added to the normal post. The handler is
   Rounds:327-359 with the two rich exception predicate replacements.
   restricted_for_fragment adds bd/name and the local-Name equality to the
   literal frozen root. Final and proposed internal terms have respectively
   three and seven closed provider/helper antecedents. They prove nothing.

   WORD branch
   stmtLowering.compile_iter_elem_copy_def:699-703 emits MLOAD/MSTORE.
   entryDecodeStaticProps.word_type_memory_size:138 derives size=32 from
   is_word_type and evaluate_type. Together with bytes=type_memory_size tv
   and sz=bytes this supplies the exact destination word capacity. Source
   word coverage and robust element representation must first be derived
   from the enclosing array; neither follows from compiler dispatch alone.

   BYTESTRING branch
   forPtrBytes.for_bytes_typed_layout:598 derives len<=cap and
   type_memory_size tv=32+32*word_size cap from type evaluation/value typing.
   for_bytes_runtime_extent and for_compile_bytes_copy_checked:613-666
   bound the actual copy count 32+ceil32(len) by this capacity and derive
   the header's untainted length from robust source representation. Payload
   need not be untainted. for_iter_bytes_copy_checked:669 is the actual
   equal-type LocMemory interface. No immutable max(32,ceil32(bytes)) bound
   is needed. Its existing pointer checker is at lo=0: using it in arbitrary
   lo entry still requires the appropriate pointer-certificate transport;
   this audit has not proved that transport or selected a new run.

   OTHER equal-type LocMemory branch, INCLUDING ZERO
   forPtrCopyInterface.for_memory_element_copy_dispatch:7-15 selects exactly
   compile_copy_memory dst src (type_memory_bytes cenv typ), not recursive
   typed copying. local_round_zero_copy above proves ONLY the compiler's
   zero-copy boundary. forPtrBulk.for_iter_bulk_copy_checked:152-178 accepts
   n=0 (no positive-size premise) but still requires source/destination
   ptr_covers, val_wf and robust source contents. Its certificate also uses
   lo=0; arbitrary-lo framing remains a proof obligation in the producer.
   No pointer or provenance requirement disappears just because n=0.

   RUNTIME PREMISE MAP AND OPEN IMPLICATIONS (not certified by quote parsing)
   - Source local PtrVar binding/type/value comes from the typed Name caller,
     supported_iterator and the array lookup, not from an assumed NONE source
     provenance. stmt_state_rel's local_ptrs_rel (loweringStateRelDefs:279-295)
     supplies the outer array local_backed, allocated-frontier bound, capacity,
     val_wf and memory_value_rel. local_region_def:175-181 interprets its base
     from that same pointer lookup. ghost_inv_at (bodyPtrDefs:128-146) supplies
     ptr_covers and universal mem_agree_outside robust array representation.
     Actual element address, coverage and robust contents must be derived at
     the MUL/ADD endpoint for this SAME run. This implication is not proved
     by the new zero-copy calculation or an independent memory execution.
   - Zero-capacity ptr_covers STILL requires a SOME provenance site (b,sz'),
     an untainted operand, a concrete pointer w and b<=w2n w<=b+sz'; see
     bodyPtrDefs.ptr_covers_def:72-77. The destination site must come from
     the ALLOCA ghost update. Fixed entry explicitly returns ptr_covers for
     arbitrary sz, including 0; dynamic prefix does too. The dynamic entry
     path alone takes supplied prefix certificates and returns G2/tn2; its
     output does not separately state ptr_covers, so that property must be
     retained through its actual assignment/check sequence in the consumer.
   - sz=type_memory_bytes cenv typ is exactly declare_local_def:723-736.
     The destination allocation history, its site/size/frontier and exterior
     local-region disjointness come from the selected fixed entry or dynamic
     prefix, then must survive condition/address/copy and future body rounds.
     Zero sz does not eliminate the allocation's site/history obligations.
   - MUL idx bytes, Dynamic-only ADD 32, then ADD saved_base remain emitted
     even at bytes=0. k<LENGTH vs and the correct header-dependent array
     capacity/layout must prove nonwrap and inside-site provenance for these
     instructions. Fixed has no tov or joff; the revised bound_op/saved_base
     freshness clauses guard tov just as the rest of the packet already did.
   - Source array snapshot must survive body/copy via iterator_unmodified,
     disjointness and old-variable frames. expr_sim_inv by itself does NOT
     preserve the value snapshot. Likewise return-buffer frame, alloca_history,
     arbitrary-lo ghost exterior, original-variable/provenance/taint frame,
     ret_pc_ok and local scope installation are actual producer obligations.
     No supplier for the full round is established in this diagnostic theory.
   - Consumers must discharge the full callback premises (ALL-H dead_lo_ok,
     frag_reachable/dalloca_no_wrap and conditional allocation included).
     Handler exceptional post must be transported to the actual popped state,
     retaining halt_exit and conditional allocation; no pointer-only projection
     suffices. Normal/Continue increment, Break, exhaustion and invariant
     restoration remain loop-assembly work, not new contract hypotheses.

   This is a bounded caller-premise audit with unresolved local implications,
   not a finding of a missing admitted foreign semantic premise and not a
   counterexample to compile_for_frag_full. C1.5.4/C1.5.5 require coordinated
   PLAN review before relying on the proposed internal contract. *)
