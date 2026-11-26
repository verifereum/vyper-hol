(* The local destination and the prepared RHS at a single store cursor. *)
Theory bodyAssignLocalPreStoreMods
Ancestors
  bodyFullPostsMods bodyFullTargetDefs bodySimFull targetPlaceSim
  bodyPtrDefs ptrDiscipline stmtSimDeclStore stmtSimDefs allocaHistory
  loweringPosts loweringStateRelDefs compileEnv context exprLowering
  exprSimProps vyperStorageFootprint vyperInterpreter vyperState vyperAST
  vyperTypeArgFits valueEncodingDefs vfmConstants venomState finite_map words

(* b is the root pointer; dw is the evaluated address of the selected
   subobject. The old source entry, not the RHS, lives at this address. *)
Definition local_assign_here_mods_def[nocompute]:
  local_assign_here_mods (DF,lo,d,ctx,func) cenv cx env st0
    (sa,es,s0,G0,tn0) (bt,id,path,dty,dst) (entry,p,cap,b,off,ptv,dw)
    ee cur s G tn <=>
    target_root bt = NameTarget id /\
    dst = (FST dst,SOME LocMemory,SOME (ValPT dty)) /\
    type_place_target env bt = SOME (Type dty) /\
    evaluate_type (get_tenv cx) dty = SOME ptv /\
    lookup_scopes id ee.scopes = SOME entry /\
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
    (?old. evaluate_subscripts entry.type entry.value path = INL old) /\
    mem_path_offset entry.type path = SOME (off,ptv) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
    lookup_var p s = SOME b /\
    local_region cenv ee.scopes s id (w2n b) cap /\
    local_backed func p s (w2n b) cap /\
    w2n b + cap <= s.vs_alloca_next /\
    off + type_memory_size ptv <= cap /\
    eval_operand (FST dst) s = SOME dw /\ w2n dw = w2n b + off /\
    lo <= w2n dw /\ op_taint tn (FST dst) = {} /\
    op_prov G (FST dst) = FLOOKUP G p /\
    (0 < type_memory_size ptv ==>
      ?x. FST dst = Var x /\ not_fresh_at cur x /\
          ptr_covers G tn x s (type_memory_size ptv)) /\
    s.vs_current_bb = cur.cs_current_bb /\
    s.vs_inst_idx = LENGTH cur.cs_current_insts /\ ~s.vs_halted /\
    alloca_history func s /\ local_ptrs_reserved cenv cur /\
    ret_pc_ok cenv cur s /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cur x) /\
    return_buf_frame d cenv cur s /\ return_buf_sep d cenv ee s /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    alloca_frame cenv es sa s0 cenv ee s /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
    (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP s.vs_allocas aid = SOME a) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    sa.cs_next_var <= cur.cs_next_var /\ sa.cs_next_id <= cur.cs_next_id /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee s /\
      storage_well_formed_on cx ee (FST H) /\
      immutable_frame_mods func cenv cx ee s /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s)
End

(* Stage through a full-layout scratch copy only when the compiler does so.
   Without staging, the bytes/string store reads the rounded live value. *)
Definition local_assign_store_source_mods_def[nocompute]:
  local_assign_store_source_mods cenv cx e vv (dty,ptv) v (dstOp,dw) (op,sw)
    sa ee cur s G tn <=>
    eval_operand dstOp s = SOME dw /\ eval_operand op s = SOME sw /\
    op_taint tn op = {} /\
    evaluate_type (get_tenv cx) dty = SOME ptv /\ value_has_type ptv v /\
    let sty = lowered_value_type cenv e in
    type_widens_to (get_tenv cx) sty dty /\
    (if is_word_type dty then
       ?etv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME etv /\
             value_has_type etv v /\ sw = typed_val_to_w256 etv v /\
             store_lays_out etv ptv v
     else
       ?stv n. ~is_word_type sty /\ evaluate_type (get_tenv cx) sty = SOME stv /\
         type_memory_bytes cenv sty = type_memory_size stv /\
         type_memory_bytes cenv dty = type_memory_size ptv /\
         value_has_type stv v /\ val_wf stv v /\ val_wf ptv v /\
         (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
              val_in_memory stv v (w2n sw) m) /\
         (if vv_location vv <> SOME LocMemory /\ is_bytestring_type dty then
            ?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
                   (?str. v = StringV str /\ len = LENGTH str)) /\
                  n = 32 + 32 * word_size len
          else n = type_memory_size stv) /\
         (0 < n ==>
            (?x. op = Var x /\ not_fresh_at cur x /\ ptr_covers G tn x s n) /\
            w2n sw + n < dimword (:256) /\ w2n sw + n <= s.vs_alloca_next) /\
         (vv_location vv = SOME LocMemory /\ 0 < n ==>
            expr_val_at cenv cx sty sa cur ee v op s \/
            ?aid. aid < cur.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (w2n sw,n) /\
                  (!name b cap. local_region cenv ee.scopes s name b cap ==>
                                regions_disjoint (w2n sw) n b cap)) /\
         (vv_location vv <> SOME LocMemory /\ ~is_bytestring_type dty /\
          ~(dty = sty \/ tuple_memory_layout_eq dty sty) ==>
            type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= w2n dw \/
            w2n dw + type_memory_size ptv <= w2n sw))
End

Theorem local_assign_here_address_mods:
  local_assign_here_mods (DF,lo,d,ctx,func) cenv cx env st0
    (sa,es,s0,G0,tn0) (bt,id,path,dty,dst) (entry,p,cap,b,off,ptv,dw)
    ee cur s G tn ==>
  type_place_target env bt = SOME (Type dty) /\
  lookup_scopes id ee.scopes = SOME entry /\
  mem_path_offset entry.type path = SOME (off,ptv) /\
  eval_operand (FST dst) s = SOME dw /\ w2n dw = w2n b + off
Proof
  simp[local_assign_here_mods_def]
QED

Theorem local_assign_source_read_mods:
  local_assign_store_source_mods cenv cx e vv (dty,ptv) v (dstOp,dw) (op,sw)
    sa ee cur s G tn /\ ~is_word_type dty /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv ==>
  eval_operand op s = SOME sw /\ op_taint tn op = {} /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (w2n sw) m)
Proof
  strip_tac >> fs[local_assign_store_source_mods_def]
QED
