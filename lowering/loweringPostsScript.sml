(* Shared pure value, place, statement and memory posts.
   These definitions precede gas certificates and simulation judgments. *)
Theory loweringPosts
Ancestors
  list rich_list finite_map pred_set pair words
  fragExec varsExt loweringSlice localPtrsProps venomMemDefs
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext vyperValue vyperAST
  valueEncoding valueEncodingProofs vyperTypeSystem
  venomExecSemantics venomInst venomState vyperLookupStorage vyperStorageBackend
Libs
  monadsyntax

Definition expr_val_rel_def:
  expr_val_rel cx t v op s <=>
    ?w. eval_operand op s = SOME w /\
        !tv. evaluate_type (get_tenv cx) t = SOME tv ==>
             if is_word_type t then w = typed_val_to_w256 tv v
             else val_in_memory tv v (w2n w) s.vs_memory
End

Definition val_footprint_def:
  val_footprint tv v =
    case v of
      BytesV bs =>
        (case tv of
           BaseTV (BytesT (Dynamic _)) => 32 + LENGTH bs
         | _ => type_memory_size tv)
    | StringV str =>
        (case tv of
           BaseTV (StringT _) => 32 + LENGTH str
         | _ => type_memory_size tv)
    | _ => type_memory_size tv
End

Definition dynarray_type_def:
  dynarray_type t <=> ?et n. t = ArrayT et (Dynamic n)
End

Definition dynarray_local_def:
  dynarray_local cenv n <=> ?t. cenv.ce_var_type n = SOME t /\ dynarray_type t
End

Definition locals_kept_def:
  locals_kept cenv es s0 s <=>
    !n b sz off len.
      local_region cenv es.scopes s0 n b sz /\ b <= off /\
      off + len <= b + sz /\ (dynarray_local cenv n ==> b + 32 <= off) ==>
      mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory
End

Definition wb_frame_def:
  wb_frame cenv es sa s0 s <=>
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es s0 s
End

Definition expr_val_at_def:
  expr_val_at cenv cx t sa sb es v op s <=>
    !tv. evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t ==>
      val_wf tv v /\
      ?w. eval_operand op s = SOME w /\
          ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b, sz) /\
                       sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
                       b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
                       (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
                                   b + sz <= lb \/ lb + lsz <= b)) \/
           (?n b sz. local_region cenv es.scopes s n b sz /\
                     b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
                     (dynarray_local cenv n /\ ~dynarray_type t ==>
                      b + 32 <= w2n w)) \/
           val_footprint tv v = 0)
End

Definition expr_post_def:
  expr_post ctx func cenv cx e es sa sb s0 es' v op s <=>
    stmt_state_rel ctx func cenv cx es' s /\
    expr_val_rel cx (expr_type e) v op s /\
    expr_val_at cenv cx (expr_type e) sa sb es' v op s /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es s0 s
End

Definition storage_holds_def:
  storage_holds cx is_transient t tv (w:bytes32) es <=>
    ?tvt v. evaluate_type (get_tenv cx) t = SOME tvt /\
            read_storage_slot cx is_transient w tvt es = (INL v, es) /\
            read_result cx tv es = (INL v, es) /\
            slots_in_range (get_storage cx es is_transient) (w2n w) tvt /\
            storage_read_live cx is_transient (get_storage cx es is_transient)
              w tvt
End

Definition sub_layout_def:
  sub_layout itv iv k tvt v <=>
    k + type_memory_size tvt <= type_memory_size itv /\
    !b mem. val_in_memory itv iv b mem ==> val_in_memory tvt v (b + k) mem
End

Definition immutable_holds_def:
  immutable_holds cenv cx t tv (w:bytes32) (es:evaluation_state) <=>
    ?name off itv iv k tvt v.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module, name) =
        SOME (ImmutableLoc off) /\ w = n2w (off + k) /\
      off + type_memory_size itv < dimword (:256) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
                 NONE => FEMPTY
               | SOME imms => get_source_immutables cenv.ce_module imms)
              name = SOME (itv, iv) /\
      evaluate_type (get_tenv cx) t = SOME tvt /\
      sub_layout itv iv k tvt v /\ value_has_type tvt v /\
      read_result cx tv es = (INL v, es)
End

Definition vv_holds_def:
  (vv_holds cenv cx t tv (StackValue t' op) es s <=>
     ?v. read_result cx tv es = (INL v, es) /\ expr_val_rel cx t v op s) /\
  (vv_holds cenv cx t tv (LocatedValue t' p) es s <=>
     t' = t /\
     ?w. eval_operand p.ptr_operand s = SOME w /\
         case p.ptr_location of
           LocMemory =>
             ?v. read_result cx tv es = (INL v, es) /\
                 !tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
                       val_in_memory tvt v (w2n w) s.vs_memory /\
                       (is_word_type t ==>
                        mem_word_at (w2n w) s.vs_memory =
                          typed_val_to_w256 tvt v)
         | LocStorage => storage_holds cx F t tv w es
         | LocTransient => storage_holds cx T t tv w es
         | LocCode => immutable_holds cenv cx t tv w es
         | LocCalldata => F)
End

Definition vv_at_def:
  (vv_at cenv cx t sa sb es tv (StackValue t' op) s <=>
     !v. read_result cx tv es = (INL v, es) ==> expr_val_at cenv cx t sa sb es v op s) /\
  (vv_at cenv cx t sa sb es tv (LocatedValue t' p) s <=>
     p.ptr_location = LocMemory ==>
     !v tvt. read_result cx tv es = (INL v, es) /\
             evaluate_type (get_tenv cx) t = SOME tvt ==>
       val_wf tvt v /\
       ?w. eval_operand p.ptr_operand s = SOME w /\
           ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b, sz) /\
                        sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
                        b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
                        (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
                                    b + sz <= lb \/ lb + lsz <= b)) \/
            (?n b sz. local_region cenv es.scopes s n b sz /\
                      b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
                      (dynarray_local cenv n /\ ~dynarray_type t ==>
                       b + 32 <= w2n w)) \/
            val_footprint tvt v = 0))
End

Definition vv_post_def:
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s <=>
    stmt_state_rel ctx func cenv cx es' s /\
    vv_holds cenv cx (expr_type e) tv vv es' s /\
    vv_at cenv cx (expr_type e) sa sb es' tv vv s /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es s0 s
End

Definition mem_field_offset_def:
  mem_field_offset [] id = NONE /\
  mem_field_offset ((name,tv)::fields) id =
    if name = id then SOME (0n,tv)
    else OPTION_MAP (\(off,ftv). (type_memory_size tv + off,ftv))
           (mem_field_offset fields id)
End

Definition mem_step_offset_def:
  mem_step_offset (StructTV fields) (AttrSubscript id) =
    mem_field_offset fields id /\
  mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) =
    (if 0 <= i /\ Num i < n then SOME (Num i * type_memory_size etv, etv)
     else NONE) /\
  mem_step_offset (ArrayTV etv (Dynamic n)) (ValueSubscript (IntV i)) =
    (if 0 <= i /\ Num i < n then SOME (32 + Num i * type_memory_size etv, etv)
     else NONE) /\
  mem_step_offset (TupleTV tvs) (ValueSubscript (IntV i)) =
    (if 0 <= i /\ Num i < LENGTH tvs then
       SOME (type_memory_size_list (TAKE (Num i) tvs), EL (Num i) tvs)
     else NONE) /\
  mem_step_offset _ _ = NONE
End

Definition mem_path_offset_def:
  mem_path_offset tv [] = SOME (0n,tv) /\
  mem_path_offset tv (sb::path) =
    case mem_step_offset tv sb of
    | NONE => NONE
    | SOME (k,etv) =>
        OPTION_MAP (\(k',ptv). (k + k',ptv)) (mem_path_offset etv path)
End

Definition slot_loc_def:
  slot_loc tr = if tr then LocTransient else LocStorage
End

Definition place_ptr_rel_def:
  (place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc vt <=>
     ?p sz b t0 tv0 k tv t.
       FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
       lookup_var p s = SOME b /\
       cenv.ce_var_type id = SOME t0 /\
       evaluate_type (get_tenv cx) t0 = SOME tv0 /\
       mem_path_offset tv0 path = SOME (k,tv) /\
       w = b + n2w k /\ loc = SOME LocMemory /\
       vt = Type t /\ evaluate_type (get_tenv cx) t = SOME tv) /\
  (place_ptr_rel cenv cx s (PlaceR (StoragePlace tr slot tv)) w loc vt <=>
     w = slot /\ loc = SOME (slot_loc tr) /\
     ?t. vt = Type t /\ evaluate_type (get_tenv cx) t = SOME tv) /\
  (place_ptr_rel cenv cx s (HashMapRef tr slot kt vt') w loc vt <=>
     w = slot /\ loc = SOME (slot_loc tr) /\ vt = HashMapT kt vt') /\
  (place_ptr_rel cenv cx s (PlaceR (ImmutablePlace src id path)) w loc vt <=>
     F) /\
  (place_ptr_rel cenv cx s (Value v) w loc vt <=> F)
End

Definition place_readable_def:
  (place_readable cx es (PlaceR (MemoryPlace id path)) <=>
     ?v. read_place cx (MemoryPlace id path) es = (INL v,es)) /\
  (place_readable cx es pv <=> T)
End

Definition target_post_def:
  target_post ctx func cenv cx es sa sb s0 es' pv vt
    (r : operand # data_location option # place_ty option) s <=>
    stmt_state_rel ctx func cenv cx es' s /\
    (?w. eval_operand (FST r) s = SOME w /\
         place_ptr_rel cenv cx s pv w (FST (SND r)) vt) /\
    SND (SND r) = SOME (value_type_place vt) /\
    (!x. FST r = Var x ==> not_fresh_at sb x) /\
    place_readable cx es' pv /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es s0 s
End

Definition stmts_env_def:
  stmts_env cenv lctx ty [] = return cenv /\
  stmts_env cenv lctx ty (s::ss) =
    do cs <- comp_get;
       if block_is_terminated cs then return cenv
       else
         do cenv' <- declare_stmt_local cenv s;
            compile_stmt cenv' lctx ty s;
            stmts_env cenv' lctx ty ss
         od
    od
End

Definition stmt_env_def:
  stmt_env cenv lctx ty s =
    do cenv' <- declare_stmt_local cenv s;
       compile_stmt cenv' lctx ty s;
       return cenv'
    od
End

Definition stmt_lands_def:
  stmt_lands lctx (sb : compile_state) (res : unit + exception) s <=>
    (res = INL () /\ s.vs_current_bb = sb.cs_current_bb /\
     s.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?ex inc. lctx = InLoop ex inc /\ s.vs_inst_idx = 0 /\
       ((res = INR BreakException /\ s.vs_current_bb = ex) \/
        (res = INR ContinueException /\ s.vs_current_bb = inc)))
End

Definition cenv_top_ext_def:
  cenv_top_ext cenv cenv' (scopes : (string |-> scope_entry) list) <=>
    cenv' with <| ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
                  ce_dynarray_capacity := cenv.ce_dynarray_capacity |> =
      cenv /\
    !n. FLOOKUP cenv'.ce_vars n <> FLOOKUP cenv.ce_vars n ==>
        (!l. FLOOKUP cenv.ce_vars n = SOME l ==> ?p sz. l = PtrVar p sz) /\
        (!l. FLOOKUP cenv'.ce_vars n = SOME l ==> ?p sz. l = PtrVar p sz) /\
        ?sc rest. scopes = sc :: rest /\ lookup_scopes n rest = NONE
End

Definition ret_pc_ok_def:
  ret_pc_ok cenv sa s <=>
    !x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
           not_fresh_at sa x /\ ?w. lookup_var x s = SOME w
End

Definition return_buf_frame_def:
  (return_buf_frame NONE (cenv : compile_env) sa s <=>
    cenv.ce_return_buf = NONE) /\
  (return_buf_frame (SOME (bw : bytes32, capacity)) cenv sa s <=>
    ?x slot_size.
      cenv.ce_return_buf = SOME (PtrVar (Var x) slot_size) /\
      lookup_var x s = SOME bw /\ not_fresh_at sa x /\
      w2n bw + capacity <= s.vs_alloca_next)
End
