Theory bodyMemEcArithCode
Ancestors
  bodyMemEcArithTransfers builtinMisc exprSimPrecompiles loweringHalt loweringStateRelDefs
  emitHelperProps emitHelper exprLoweringProps context compileEnv venomInst

(* Restatement of private exprSimECArith.ec_input_stores_shape;
   original: alan-ref/base/exprSimECArithScript.sml.txt, lines 785-823. *)
Theorem ec_input_stores_shape:
  (!p1 p2 ib sa sb. (do xp <- emit_op ADD [p1; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p1; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp2 <- emit_op ADD [p2; Lit 0w];
      x2 <- emit_op MLOAD [xp2];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; x2];
      yp2 <- emit_op ADD [p2; Lit 32w];
      y2 <- emit_op MLOAD [yp2];
      dst3 <- emit_op ADD [ib; Lit 96w];
      emit_void MSTORE [dst3; y2] od) sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 12 /\
  sb.cs_next_id = sa.cs_next_id + 16) /\
  (!p ib scalar sa sb. (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; scalar] od) sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 7 /\
  sb.cs_next_id = sa.cs_next_id + 10)
Proof
  conj_tac >> rpt gen_tac >>
  simp[emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def]
QED

(* Family-specific restatement of private exprSimECArith.ec_points_prefix,
   first conjunct, original reference lines 1297-1333. *)
Theorem ecmul_points_prefix:
  compile_ecmul_point p scalar sf = (res,sb) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) ==>
  ?ib ob sa sp sm.
    context$compile_alloc_buffer 96 sf = (ib,sa) /\
    (do xp <- emit_op ADD [p; Lit 0w];
        x <- emit_op MLOAD [xp];
        dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
        emit_void MSTORE [dst0; x];
        yp <- emit_op ADD [p; Lit 32w];
        y <- emit_op MLOAD [yp];
        dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [dst1; y];
        dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [dst2; scalar] od) sa = ((),sp) /\
    context$compile_alloc_buffer 64 sp = (ob,sm) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit 7w; ib.buf_operand; Lit 96w; ob.buf_operand; Lit 64w];
        emit_void ASSERT [success]; return ob.buf_operand od) sm = (res,sb) /\
    emitted_insts sf sm = emitted_insts sf sa ++ emitted_insts sa sp ++
      emitted_insts sp sm /\
    emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 96w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sp.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sp /\
    local_ptrs_reserved cenv sm /\
    sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sp.cs_next_var /\
    sp.cs_next_var <= sm.cs_next_var /\
    sf.cs_next_id < sa.cs_next_id /\ sa.cs_next_id <= sp.cs_next_id /\
    sp.cs_next_id < sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
    (?x. ib.buf_operand = Var x /\ not_fresh_at sa x /\ not_fresh_at sm x) /\
    (?x. ob.buf_operand = Var x /\ not_fresh_at sm x)
Proof
  strip_tac >>
  qpat_x_assum `_ sf = (res,sb)` mp_tac >>
  simp[compile_ecmul_point_def] >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `context$compile_alloc_buffer _ sf = (ib,sa)` >>
  qpat_x_assum `_ sa = (res,sb)` mp_tac >>
  simp[Once comp_bind_def, comp_return_def] >> strip_tac >>
  qpat_abbrev_tac `payload = comp_bind (emit_op ADD _) _` >>
  qmatch_asmsub_abbrev_tac `comp_bind (context$compile_alloc_buffer 64) suffix` >>
  qabbrev_tac `tail = comp_bind (context$compile_alloc_buffer 64) suffix` >>
  `comp_ignore_bind payload tail sa = (res,sb)` by
    (fs[Abbr `payload`, Abbr `tail`, comp_ignore_bind_def, comp_bind_assoc]) >>
  pop_assum mp_tac >>
  simp[comp_ignore_bind_def, Once comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `payload sa = (u,sp)` >> Cases_on `u` >>
  qpat_x_assum `tail sp = _` mp_tac >>
  simp[Abbr `tail`, Once comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `context$compile_alloc_buffer 64 sp = (ob,sm)` >>
  qunabbrev_tac `payload` >> imp_res_tac ec_input_stores_shape >>
  qunabbrev_tac `suffix` >> fs[] >>
  qpat_x_assum `_ sm = (res,sb)` mp_tac >>
  simp[Once comp_bind_def, comp_return_def] >> strip_tac >>
  drule computed_suffix_shape >> strip_tac >>
  drule_then strip_assume_tac compile_alloc_buffer_insts >>
  rev_drule_then strip_assume_tac compile_alloc_buffer_insts >>
  `emitted_insts sf sm = emitted_insts sf sa ++
     emitted_insts sa sp ++ emitted_insts sp sm` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1] >>
     simp[emitted_insts_def, NoAsms] >> simp[rich_listTheory.DROP_APPEND1]) >>
  qpat_x_assum `emitted_insts sm sb = _` kall_tac >>
  `sm.cs_current_insts = sf.cs_current_insts ++ emitted_insts sf sm` by
    (CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV emitted_insts_def))) >>
     simp[rich_listTheory.DROP_APPEND1, listTheory.APPEND_ASSOC]) >>
  `emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  qpat_x_assum `sm.cs_current_insts = sf.cs_current_insts ++ _` kall_tac >>
  drule_then strip_assume_tac compile_alloc_buffer_parts >>
  rev_drule_then strip_assume_tac compile_alloc_buffer_parts >>
  gvs[GSYM comp_ignore_bind_def] >>
  conj_tac
  >- (qpat_x_assum `!i. _ ==> MEM i (fn_insts func)` irule >>
      simp[] >> disj1_tac >> disj1_tac >>
      once_rewrite_tac[emitted_insts_def] >> simp[rich_listTheory.DROP_APPEND1]) >>
  conj_tac
  >- (qpat_x_assum `!i. _ ==> MEM i (fn_insts func)` irule >>
      simp[] >> disj1_tac >> disj2_tac >>
      once_rewrite_tac[emitted_insts_def] >> simp[rich_listTheory.DROP_APPEND1]) >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[]) >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[]) >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[]) >>
  simp[not_fresh_at_def]
QED

(* Family-specific restatement of private exprSimECArith.ec_points_prefix,
   second conjunct, original reference lines 1334-1375. *)
Theorem ecadd_points_prefix:
  compile_ecadd_points p1 p2 sf = (res,sb) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) ==>
  ?ib ob sa sp sm.
    context$compile_alloc_buffer 128 sf = (ib,sa) /\
    (do xp <- emit_op ADD [p1; Lit 0w];
        x <- emit_op MLOAD [xp];
        dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
        emit_void MSTORE [dst0; x];
        yp <- emit_op ADD [p1; Lit 32w];
        y <- emit_op MLOAD [yp];
        dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [dst1; y];
        xp2 <- emit_op ADD [p2; Lit 0w];
        x2 <- emit_op MLOAD [xp2];
        dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [dst2; x2];
        yp2 <- emit_op ADD [p2; Lit 32w];
        y2 <- emit_op MLOAD [yp2];
        dst3 <- emit_op ADD [ib.buf_operand; Lit 96w];
        emit_void MSTORE [dst3; y2] od) sa = ((),sp) /\
    context$compile_alloc_buffer 64 sp = (ob,sm) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit 6w; ib.buf_operand; Lit 128w; ob.buf_operand; Lit 64w];
        emit_void ASSERT [success]; return ob.buf_operand od) sm = (res,sb) /\
    emitted_insts sf sm = emitted_insts sf sa ++ emitted_insts sa sp ++
      emitted_insts sp sm /\
    emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sp.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sp /\
    local_ptrs_reserved cenv sm /\
    sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sp.cs_next_var /\
    sp.cs_next_var <= sm.cs_next_var /\
    sf.cs_next_id < sa.cs_next_id /\ sa.cs_next_id <= sp.cs_next_id /\
    sp.cs_next_id < sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
    (?x. ib.buf_operand = Var x /\ not_fresh_at sa x /\ not_fresh_at sm x) /\
    (?x. ob.buf_operand = Var x /\ not_fresh_at sm x)
Proof
  strip_tac >>
  qpat_x_assum `_ sf = (res,sb)` mp_tac >>
  simp[compile_ecadd_points_def] >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `context$compile_alloc_buffer _ sf = (ib,sa)` >>
  qpat_x_assum `_ sa = (res,sb)` mp_tac >>
  simp[Once comp_bind_def, comp_return_def] >> strip_tac >>
  qpat_abbrev_tac `payload = comp_bind (emit_op ADD _) _` >>
  qmatch_asmsub_abbrev_tac `comp_bind (context$compile_alloc_buffer 64) suffix` >>
  qabbrev_tac `tail = comp_bind (context$compile_alloc_buffer 64) suffix` >>
  `comp_ignore_bind payload tail sa = (res,sb)` by
    (fs[Abbr `payload`, Abbr `tail`, comp_ignore_bind_def, comp_bind_assoc]) >>
  pop_assum mp_tac >>
  simp[comp_ignore_bind_def, Once comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `payload sa = (u,sp)` >> Cases_on `u` >>
  qpat_x_assum `tail sp = _` mp_tac >>
  simp[Abbr `tail`, Once comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `context$compile_alloc_buffer 64 sp = (ob,sm)` >>
  qunabbrev_tac `payload` >> imp_res_tac ec_input_stores_shape >>
  qunabbrev_tac `suffix` >> fs[] >>
  qpat_x_assum `_ sm = (res,sb)` mp_tac >>
  simp[Once comp_bind_def, comp_return_def] >> strip_tac >>
  drule computed_suffix_shape >> strip_tac >>
  drule_then strip_assume_tac compile_alloc_buffer_insts >>
  rev_drule_then strip_assume_tac compile_alloc_buffer_insts >>
  `emitted_insts sf sm = emitted_insts sf sa ++
     emitted_insts sa sp ++ emitted_insts sp sm` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1] >>
     simp[emitted_insts_def, NoAsms] >> simp[rich_listTheory.DROP_APPEND1]) >>
  qpat_x_assum `emitted_insts sm sb = _` kall_tac >>
  `sm.cs_current_insts = sf.cs_current_insts ++ emitted_insts sf sm` by
    (CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV emitted_insts_def))) >>
     simp[rich_listTheory.DROP_APPEND1, listTheory.APPEND_ASSOC]) >>
  `emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  qpat_x_assum `sm.cs_current_insts = sf.cs_current_insts ++ _` kall_tac >>
  drule_then strip_assume_tac compile_alloc_buffer_parts >>
  rev_drule_then strip_assume_tac compile_alloc_buffer_parts >>
  gvs[GSYM comp_ignore_bind_def] >>
  conj_tac
  >- (qpat_x_assum `!i. _ ==> MEM i (fn_insts func)` irule >>
      simp[] >> disj1_tac >> disj1_tac >>
      once_rewrite_tac[emitted_insts_def] >> simp[rich_listTheory.DROP_APPEND1]) >>
  conj_tac
  >- (qpat_x_assum `!i. _ ==> MEM i (fn_insts func)` irule >>
      simp[] >> disj1_tac >> disj2_tac >>
      once_rewrite_tac[emitted_insts_def] >> simp[rich_listTheory.DROP_APPEND1]) >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[]) >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[]) >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[]) >>
  simp[not_fresh_at_def]
QED

Theorem ecmul_prefix_code:
  context$compile_alloc_buffer 96 sf = (ib,sa) /\
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [dst2; scalar] od) sa = ((),sp) /\
  context$compile_alloc_buffer 64 sp = (ob,sm) ==>
  MAP (\i. i.inst_opcode) (emitted_insts sf sm) =
    [ALLOCA; ADD; MLOAD; ADD; MSTORE; ADD; MLOAD; ADD; MSTORE; ADD; MSTORE; ALLOCA] /\
  LENGTH (emitted_insts sf sm) = 12 /\
  sm.cs_current_insts = sf.cs_current_insts ++ emitted_insts sf sm /\
  same_blocks sf sm /\
  (!i. MEM i (emitted_insts sf sm) ==>
    MEM i.inst_opcode [ALLOCA; ADD; MLOAD; MSTORE])
Proof
  simp[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def,
       mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem ecadd_prefix_code:
  context$compile_alloc_buffer 128 sf = (ib,sa) /\
  (do xp <- emit_op ADD [p1; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p1; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp2 <- emit_op ADD [p2; Lit 0w];
      x2 <- emit_op MLOAD [xp2];
      dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [dst2; x2];
      yp2 <- emit_op ADD [p2; Lit 32w];
      y2 <- emit_op MLOAD [yp2];
      dst3 <- emit_op ADD [ib.buf_operand; Lit 96w];
      emit_void MSTORE [dst3; y2] od) sa = ((),sp) /\
  context$compile_alloc_buffer 64 sp = (ob,sm) ==>
  MAP (\i. i.inst_opcode) (emitted_insts sf sm) =
    [ALLOCA; ADD; MLOAD; ADD; MSTORE; ADD; MLOAD; ADD; MSTORE;
     ADD; MLOAD; ADD; MSTORE; ADD; MLOAD; ADD; MSTORE; ALLOCA] /\
  LENGTH (emitted_insts sf sm) = 18 /\
  sm.cs_current_insts = sf.cs_current_insts ++ emitted_insts sf sm /\
  same_blocks sf sm /\
  (!i. MEM i (emitted_insts sf sm) ==>
    MEM i.inst_opcode [ALLOCA; ADD; MLOAD; MSTORE])
Proof
  simp[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def,
       mk_inst_def] >> rpt strip_tac >> gvs[]
QED
