Theory bodyPtrPrecompileBuiltinsCompilerStages
Ancestors builtinMisc context compileEnv loweringStateRelDefs emitHelper exprSimPrecompiles
          exprLoweringProps loweringHalt rich_list

Theorem compiler_append_trans:
  s1.cs_current_insts = s0.cs_current_insts ++ emitted_insts s0 s1 /\
  s2.cs_current_insts = s1.cs_current_insts ++ emitted_insts s1 s2 ==>
  s2.cs_current_insts = s0.cs_current_insts ++ emitted_insts s0 s2 /\
  emitted_insts s0 s2 = emitted_insts s0 s1 ++ emitted_insts s1 s2
Proof
  strip_tac >> drule_all emitted_insts_append >>
  strip_tac >> metis_tac[APPEND_ASSOC]
QED

Theorem computed_load_suffix_compiler_shape:
  comp_bind
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit target; ip; Lit insz; op; Lit outsz];
        emit_void ASSERT [success]; return op od)
    (\out. emit_op MLOAD [out]) sm = (res,sb) ==>
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  same_blocks sm sb /\ sb.cs_next_var = sm.cs_next_var + 3 /\
  sb.cs_next_id = sm.cs_next_id + 4
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def, DROP_APPEND1, same_blocks_def]
QED

(* Finite compiler progress; offsets and operands are arbitrary. *)
Theorem word_transfer_compiler_shape:
  (do src <- emit_op ADD [p; Lit poff]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit boff]; emit_void MSTORE [dst; value] od)
    sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 3 /\
  sb.cs_next_id = sa.cs_next_id + 4
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def, DROP_APPEND1, same_blocks_def]
QED

Theorem offset_store_compiler_shape:
  (do dst <- emit_op ADD [buf; Lit off]; emit_void MSTORE [dst; v] od)
    sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 1 /\
  sb.cs_next_id = sa.cs_next_id + 2
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def, DROP_APPEND1, same_blocks_def]
QED

Theorem direct_store_compiler_shape:
  emit_void MSTORE [buf; v] sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var /\
  sb.cs_next_id = sa.cs_next_id + 1
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def, DROP_APPEND1, same_blocks_def]
QED

(* Group the actual compiler operations at the boundaries certified by the
   pointer staging lemmas.  No runtime or ghost claim is hidden here. *)
Theorem ecmul_compiler_grouped:
  compile_ecmul_point p scalar =
  (do ib <- compile_alloc_buffer 96;
      (do src <- emit_op ADD [p; Lit 0w];
          value <- emit_op MLOAD [src];
          dst <- emit_op ADD [ib.buf_operand; Lit 0w];
          emit_void MSTORE [dst; value] od);
      (do src <- emit_op ADD [p; Lit 32w];
          value <- emit_op MLOAD [src];
          dst <- emit_op ADD [ib.buf_operand; Lit 32w];
          emit_void MSTORE [dst; value] od);
      (do dst <- emit_op ADD [ib.buf_operand; Lit 64w];
          emit_void MSTORE [dst; scalar] od);
      ob <- compile_alloc_buffer 64;
      (do gas <- emit_op GAS [];
          success <- emit_op STATICCALL
            [gas; Lit 7w; ib.buf_operand; Lit 96w; ob.buf_operand; Lit 64w];
          emit_void ASSERT [success]; return ob.buf_operand od) od)
Proof
  simp[compile_ecmul_point_def, comp_ignore_bind_def, comp_bind_assoc] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

Theorem ecadd_compiler_grouped:
  compile_ecadd_points p q =
  (do ib <- compile_alloc_buffer 128;
      (do src <- emit_op ADD [p; Lit 0w]; value <- emit_op MLOAD [src];
          dst <- emit_op ADD [ib.buf_operand; Lit 0w];
          emit_void MSTORE [dst; value] od);
      (do src <- emit_op ADD [p; Lit 32w]; value <- emit_op MLOAD [src];
          dst <- emit_op ADD [ib.buf_operand; Lit 32w];
          emit_void MSTORE [dst; value] od);
      (do src <- emit_op ADD [q; Lit 0w]; value <- emit_op MLOAD [src];
          dst <- emit_op ADD [ib.buf_operand; Lit 64w];
          emit_void MSTORE [dst; value] od);
      (do src <- emit_op ADD [q; Lit 32w]; value <- emit_op MLOAD [src];
          dst <- emit_op ADD [ib.buf_operand; Lit 96w];
          emit_void MSTORE [dst; value] od);
      ob <- compile_alloc_buffer 64;
      (do gas <- emit_op GAS [];
          success <- emit_op STATICCALL
            [gas; Lit 6w; ib.buf_operand; Lit 128w; ob.buf_operand; Lit 64w];
          emit_void ASSERT [success]; return ob.buf_operand od) od)
Proof
  simp[compile_ecadd_points_def, comp_ignore_bind_def, comp_bind_assoc] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

Theorem recovery_compiler_grouped:
  compile_ecrecover h v r sig =
  (do ib <- compile_alloc_buffer 128;
      emit_void MSTORE [ib.buf_operand; h];
      (do dst <- emit_op ADD [ib.buf_operand; Lit 32w];
          emit_void MSTORE [dst; v] od);
      (do dst <- emit_op ADD [ib.buf_operand; Lit 64w];
          emit_void MSTORE [dst; r] od);
      (do dst <- emit_op ADD [ib.buf_operand; Lit 96w];
          emit_void MSTORE [dst; sig] od);
      ob <- compile_alloc_buffer 32;
      emit_void MSTORE [ob.buf_operand; Lit 0w];
      comp_bind
        (do gas <- emit_op GAS [];
            success <- emit_op STATICCALL
              [gas; Lit 1w; ib.buf_operand; Lit 128w; ob.buf_operand; Lit 32w];
            emit_void ASSERT [success]; return ob.buf_operand od)
        (\out. emit_op MLOAD [out]) od)
Proof
  simp[compile_ecrecover_def, comp_ignore_bind_def, comp_bind_assoc] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

Theorem ecmul_compiler_stages:
  compile_ecmul_point p scalar sf = (res,sb) ==>
  ?ib sa s1 s2 sp ob sm.
    compile_alloc_buffer 96 sf = (ib,sa) /\
    (do src <- emit_op ADD [p; Lit 0w]; value <- emit_op MLOAD [src];
        dst <- emit_op ADD [ib.buf_operand; Lit 0w];
        emit_void MSTORE [dst; value] od) sa = ((),s1) /\
    (do src <- emit_op ADD [p; Lit 32w]; value <- emit_op MLOAD [src];
        dst <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [dst; value] od) s1 = ((),s2) /\
    (do dst <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [dst; scalar] od) s2 = ((),sp) /\
    compile_alloc_buffer 64 sp = (ob,sm) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit 7w; ib.buf_operand; Lit 96w; ob.buf_operand; Lit 64w];
        emit_void ASSERT [success]; return ob.buf_operand od) sm = (res,sb) /\
    sp.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sp /\
    sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
    same_blocks sa sp /\ sp.cs_next_var = sa.cs_next_var + 7 /\
    sp.cs_next_id = sa.cs_next_id + 10 /\
    sb.cs_next_id = sm.cs_next_id + 3
Proof
  rewrite_tac[ecmul_compiler_grouped] >>
  simp[Once comp_bind_def] >> pairarg_tac >>
  simp[] >> strip_tac >>
  ntac 3
    (qpat_x_assum `_ _ = (res,sb)` mp_tac >>
     simp[comp_ignore_bind_def, Once comp_bind_def] >>
     pairarg_tac >> simp[] >> strip_tac) >>
  qpat_x_assum `comp_bind (compile_alloc_buffer 64) _ _ = _` mp_tac >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[oneTheory.one, GSYM comp_ignore_bind_def] >>
  imp_res_tac word_transfer_compiler_shape >>
  imp_res_tac offset_store_compiler_shape >>
  drule computed_suffix_shape >> strip_tac >>
  imp_res_tac compiler_append_trans >> gvs[same_blocks_def]
QED

Theorem ecadd_compiler_stages:
  compile_ecadd_points p q sf = (res,sb) ==>
  ?ib sa s1 s2 s3 sp ob sm.
    compile_alloc_buffer 128 sf = (ib,sa) /\
    (do src <- emit_op ADD [p; Lit 0w]; value <- emit_op MLOAD [src];
        dst <- emit_op ADD [ib.buf_operand; Lit 0w];
        emit_void MSTORE [dst; value] od) sa = ((),s1) /\
    (do src <- emit_op ADD [p; Lit 32w]; value <- emit_op MLOAD [src];
        dst <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [dst; value] od) s1 = ((),s2) /\
    (do src <- emit_op ADD [q; Lit 0w]; value <- emit_op MLOAD [src];
        dst <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [dst; value] od) s2 = ((),s3) /\
    (do src <- emit_op ADD [q; Lit 32w]; value <- emit_op MLOAD [src];
        dst <- emit_op ADD [ib.buf_operand; Lit 96w];
        emit_void MSTORE [dst; value] od) s3 = ((),sp) /\
    compile_alloc_buffer 64 sp = (ob,sm) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit 6w; ib.buf_operand; Lit 128w; ob.buf_operand; Lit 64w];
        emit_void ASSERT [success]; return ob.buf_operand od) sm = (res,sb) /\
    sp.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sp /\
    sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
    same_blocks sa sp /\ sp.cs_next_var = sa.cs_next_var + 12 /\
    sp.cs_next_id = sa.cs_next_id + 16 /\
    sb.cs_next_id = sm.cs_next_id + 3
Proof
  rewrite_tac[ecadd_compiler_grouped] >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  ntac 4
    (qpat_x_assum `_ _ = (res,sb)` mp_tac >>
     simp[comp_ignore_bind_def, Once comp_bind_def] >>
     pairarg_tac >> simp[] >> strip_tac) >>
  qpat_x_assum `comp_bind (compile_alloc_buffer 64) _ _ = _` mp_tac >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[oneTheory.one, GSYM comp_ignore_bind_def] >>
  imp_res_tac word_transfer_compiler_shape >>
  drule computed_suffix_shape >> strip_tac >>
  imp_res_tac compiler_append_trans >> gvs[same_blocks_def]
QED

Theorem recovery_compiler_stages:
  compile_ecrecover h v r sig sf = (res,sb) ==>
  ?ib sa s0 s1 s2 sp ob so sm.
    compile_alloc_buffer 128 sf = (ib,sa) /\
    emit_void MSTORE [ib.buf_operand; h] sa = ((),s0) /\
    (do dst <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [dst; v] od) s0 = ((),s1) /\
    (do dst <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [dst; r] od) s1 = ((),s2) /\
    (do dst <- emit_op ADD [ib.buf_operand; Lit 96w];
        emit_void MSTORE [dst; sig] od) s2 = ((),sp) /\
    compile_alloc_buffer 32 sp = (ob,so) /\
    emit_void MSTORE [ob.buf_operand; Lit 0w] so = ((),sm) /\
    comp_bind
      (do gas <- emit_op GAS [];
          success <- emit_op STATICCALL
            [gas; Lit 1w; ib.buf_operand; Lit 128w; ob.buf_operand; Lit 32w];
          emit_void ASSERT [success]; return ob.buf_operand od)
      (\out. emit_op MLOAD [out]) sm = (res,sb) /\
    sp.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sp /\
    sm.cs_current_insts = so.cs_current_insts ++ emitted_insts so sm /\
    sb.cs_current_insts = so.cs_current_insts ++ emitted_insts so sb /\
    same_blocks sa sp /\ sp.cs_next_var = sa.cs_next_var + 3 /\
    sp.cs_next_id = sa.cs_next_id + 7 /\
    sm.cs_next_var = so.cs_next_var /\ sm.cs_next_id = so.cs_next_id + 1
Proof
  rewrite_tac[recovery_compiler_grouped] >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  ntac 4
    (qpat_x_assum `_ _ = (res,sb)` mp_tac >>
     simp[comp_ignore_bind_def, Once comp_bind_def] >>
     pairarg_tac >> simp[] >> strip_tac) >>
  qpat_x_assum `comp_bind (compile_alloc_buffer 32) _ _ = _` mp_tac >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `_ _ = (res,sb)` mp_tac >>
  simp[comp_ignore_bind_def, Once comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  gvs[oneTheory.one, GSYM comp_ignore_bind_def] >>
  imp_res_tac direct_store_compiler_shape >>
  imp_res_tac offset_store_compiler_shape >>
  drule computed_load_suffix_compiler_shape >> strip_tac >>
  imp_res_tac compiler_append_trans >> gvs[same_blocks_def]
QED


(* A compiler-only frame for two allocations separated by an arbitrary
   instruction-appending payload.  The suffix may append any instructions. *)
Theorem allocated_stage_frame:
  compile_alloc_buffer ni sf = (ib,sa) /\
  compile_alloc_buffer no sp = (ob,sm) /\
  sp.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sp /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  sa.cs_next_var <= sp.cs_next_var /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) ==>
  emitted_insts sf sm = emitted_insts sf sa ++ emitted_insts sa sp ++
    emitted_insts sp sm /\
  emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit (n2w ni)]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst sp.cs_next_id ALLOCA [Lit (n2w no)]
    [STRING #"%" (toString sp.cs_next_var)]) (fn_insts func) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sp /\
  local_ptrs_reserved cenv sm /\
  sf.cs_next_var < sa.cs_next_var /\ sp.cs_next_var < sm.cs_next_var /\
  sf.cs_next_id < sa.cs_next_id /\ sp.cs_next_id < sm.cs_next_id /\
  (?x. ib.buf_operand = Var x /\ not_fresh_at sa x /\ not_fresh_at sm x) /\
  (?x. ob.buf_operand = Var x /\ not_fresh_at sm x)
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `sp.cs_current_insts = sa.cs_current_insts ++ payload` >>
  qmatch_asmsub_abbrev_tac `sb.cs_current_insts = sm.cs_current_insts ++ suffix` >>
  drule_all compile_alloc_buffer_insts >> strip_tac >>
  drule_all compile_alloc_buffer_parts >> strip_tac >>
  qpat_assum `compile_alloc_buffer ni sf = _`
    (mp_then Any strip_assume_tac compile_alloc_buffer_insts) >>
  qpat_assum `compile_alloc_buffer ni sf = _`
    (mp_then Any strip_assume_tac compile_alloc_buffer_parts) >>
  gvs[emitted_insts_def, DROP_APPEND1, APPEND_ASSOC] >>
  conj_tac >-
    (irule local_ptrs_reserved_next_var >> qexists `sf` >> simp[]) >>
  conj_tac >-
    (irule local_ptrs_reserved_next_var >> qexists `sf` >> simp[]) >>
  conj_tac >-
    (irule local_ptrs_reserved_next_var >> qexists `sf` >> simp[]) >>
  gvs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac
QED

(* These consumer probes discharge the compiler-frame premises from each
   real compiler, rather than requiring a caller to assume allocation facts. *)
Theorem ecmul_compiler_allocation_members:
  compile_ecmul_point p scalar sf = (res,sb) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) ==>
  ?ib sa sp ob sm.
    compile_alloc_buffer 96 sf = (ib,sa) /\
    compile_alloc_buffer 64 sp = (ob,sm) /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 96w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sp.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sp /\
    local_ptrs_reserved cenv sm
Proof
  strip_tac >> drule ecmul_compiler_stages >> strip_tac >>
  `sa.cs_next_var <= sp.cs_next_var` by simp[] >>
  drule_all allocated_stage_frame >> strip_tac >> metis_tac[]
QED

Theorem ecadd_compiler_allocation_members:
  compile_ecadd_points p q sf = (res,sb) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) ==>
  ?ib sa sp ob sm.
    compile_alloc_buffer 128 sf = (ib,sa) /\
    compile_alloc_buffer 64 sp = (ob,sm) /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sp.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sp /\
    local_ptrs_reserved cenv sm
Proof
  strip_tac >> drule ecadd_compiler_stages >> strip_tac >>
  `sa.cs_next_var <= sp.cs_next_var` by simp[] >>
  drule_all allocated_stage_frame >> strip_tac >> metis_tac[]
QED

Theorem recovery_compiler_allocation_members:
  compile_ecrecover h v r sig sf = (res,sb) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) ==>
  ?ib sa sp ob so sm.
    compile_alloc_buffer 128 sf = (ib,sa) /\
    compile_alloc_buffer 32 sp = (ob,so) /\
    emit_void MSTORE [ob.buf_operand; Lit 0w] so = ((),sm) /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sp.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sp.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sp /\
    local_ptrs_reserved cenv so /\ local_ptrs_reserved cenv sm
Proof
  strip_tac >> drule recovery_compiler_stages >> strip_tac >>
  `sa.cs_next_var <= sp.cs_next_var` by simp[] >>
  drule_all allocated_stage_frame >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists `so` >> simp[]) >>
  metis_tac[]
QED
