(* Closed, production CREATE preparation intervals and the nested call rule. *)
Theory createSizePreparationCode
Ancestors
  createSizeCreateLayoutCode createSizeFixedPreparation createSizeConcreteSnapshots
  createSizeEncodeCode createSizeLocationCode createSizeResultCheckCode
  createSizeCutCode dallocaCreateGeometry exprLowering builtinCreate context
  compileEnv emitHelper venomInst pair

Theorem preparation_run_cuts[local]:
  (!opc ops a x b. emit_op opc ops a = (x,b) /\
      create_cut_targets opc ops = [] ==> create_cut_code {} a b) /\
  (!opc ops a x b. emit_void opc ops a = (x,b) /\
      create_cut_targets opc ops = [] ==> create_cut_code {} a b) /\
  (!n a x b. compile_alloc_dynamic n a = (x,b) ==> create_cut_code {} a b) /\
  (!dst src n a x b. compile_copy_memory_dynamic dst src n a = (x,b) ==>
      create_cut_code {} a b) /\
  (!n a x b. compile_alloc_buffer n a = (x,b) ==> create_cut_code {} a b) /\
  (!ce dst rows a x b. compile_abi_encode_values_to_buf ce dst rows a = (x,b) ==>
      create_cut_code {} a b) /\
  (!ce vv ty a x b. compile_create_snapshot ce vv ty a = (x,b) ==>
      create_cut_code {} a b) /\
  (!ce copy vv a x b. compile_snapshot_vv ce copy vv a = (x,b) ==>
      create_cut_code {} a b) /\
  (!ce vv a x b. unwrap_value ce vv a = (x,b) ==> create_cut_code {} a b)
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- metis_tac[create_cut_code_emit_op, pairTheory.SND, listTheory.MEM]
  >- metis_tac[create_cut_code_emit_void, pairTheory.SND, listTheory.MEM]
  >- (`create_cut_code {} a (SND (compile_alloc_dynamic n a))` by
        (pure_rewrite_tac[compile_alloc_dynamic_def] >>
         irule create_cut_code_emit_op >> simp[create_cut_targets_def]) >>
      pop_assum mp_tac >> simp[])
  >- (`create_cut_code {} a (SND (compile_copy_memory_dynamic dst src n a))` by
        (pure_rewrite_tac[compile_copy_memory_dynamic_def] >>
         irule create_cut_code_emit_void >> simp[create_cut_targets_def]) >>
      pop_assum mp_tac >> simp[])
  >- (`create_cut_code {} a (SND (compile_alloc_buffer n a))` by
        (pure_rewrite_tac[compile_alloc_buffer_def] >> irule create_cut_code_bind >>
         simp[create_cut_code_emit_op, create_cut_targets_def]) >>
      pop_assum mp_tac >> simp[])
  >- metis_tac[create_encode_values_cut_code, pairTheory.SND]
  >- metis_tac[create_bytecode_snapshot_cut_code, pairTheory.SND]
  >- metis_tac[create_vv_snapshot_cut_code, pairTheory.SND]
  >> metis_tac[create_unwrap_cut_code, pairTheory.SND]
QED

val preparation_step = FIRST (map (fn th =>
  irule th >> goal_assum (drule_at Any) >> simp[create_cut_targets_def] >> NO_TAC)
  (CONJUNCTS preparation_run_cuts));

fun preparation_join cuts =
  map_every (fn cut => irule create_cut_code_join >> qexists_tac cut >>
    (reverse conj_tac >- preparation_step)) cuts >> preparation_step;

(* These runs stop before the next operand or the dispatch. Constructor-row
   snapshots themselves use create_vv_snapshot_cut_code at each row. *)
Theorem create_preparation_cut_code:
  (!ce vv ty a bytes m len n data b.
      compile_create_snapshot ce vv ty a = (bytes,m) /\
      emit_op MLOAD [bytes] m = (len,n) /\
      emit_op ADD [bytes;Lit 32w] n = (data,b) ==> create_cut_code {} a b) /\
  (!ce copy vv a snap m ptr n len p data b.
      compile_snapshot_vv ce copy vv a = (snap,m) /\
      unwrap_value ce snap m = (ptr,n) /\
      emit_op MLOAD [ptr] n = (len,p) /\
      emit_op ADD [ptr;Lit 32w] p = (data,b) ==> create_cut_code {} a b) /\
  (!ce size rows a buf m len b.
      compile_alloc_buffer size a = (buf,m) /\
      compile_abi_encode_values_to_buf ce buf.buf_operand rows m = (len,b) ==>
      create_cut_code {} a b) /\
  (!ce size data len rows a buf m n dst p args_len q total b.
      compile_alloc_buffer size a = (buf,m) /\
      compile_copy_memory_dynamic buf.buf_operand data len m = ((),n) /\
      emit_op ADD [buf.buf_operand;len] n = (dst,p) /\
      compile_abi_encode_values_to_buf ce dst rows p = (args_len,q) /\
      emit_op ADD [len;args_len] q = (total,b) ==> create_cut_code {} a b) /\
  (!target a code a1 a2 shifted a3 preamble a4 size a5 alloc_ptr a6 a7
      code_dst a8 a9 buf a10 len sc.
      emit_op EXTCODESIZE [target] a = (code,a1) /\
      emit_void ASSERT [code] a1 = ((),a2) /\
      emit_op SHL [Lit 56w;code] a2 = (shifted,a3) /\
      emit_op OR [Lit 0x620000003d81600b3d39f3w;shifted] a3 = (preamble,a4) /\
      emit_op ADD [code;Lit 32w] a4 = (size,a5) /\
      compile_alloc_dynamic size a5 = (alloc_ptr,a6) /\
      emit_void MSTORE [alloc_ptr;preamble] a6 = ((),a7) /\
      emit_op ADD [alloc_ptr;Lit 32w] a7 = (code_dst,a8) /\
      emit_void EXTCODECOPY [target;code_dst;Lit 0w;code] a8 = ((),a9) /\
      emit_op ADD [alloc_ptr;Lit 21w] a9 = (buf,a10) /\
      emit_op ADD [code;Lit 11w] a10 = (len,sc) ==> create_cut_code {} a sc) /\
  (!target offset code args_ptr args_len a size sm alloc_ptr sn se sc.
      emit_op ADD [code;args_len] a = (size,sm) /\
      compile_alloc_dynamic size sm = (alloc_ptr,sn) /\
      emit_void EXTCODECOPY [target;alloc_ptr;offset;code] sn = ((),se) /\
      (if args_len = Lit 0w then sc = se else
         ?args_dest sx.
           emit_op ADD [alloc_ptr;code] se = (args_dest,sx) /\
           compile_copy_memory_dynamic args_dest args_ptr args_len sx = ((),sc)) ==>
      create_cut_code {} a sc)
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- preparation_join [`n`,`m`]
  >- preparation_join [`p`,`n`,`m`]
  >- preparation_join [`m`]
  >- preparation_join [`q`,`p`,`n`,`m`]
  >- preparation_join [`a10`,`a9`,`a8`,`a7`,`a6`,`a5`,`a4`,`a3`,`a2`,`a1`]
  >> `create_cut_code {} a se` by preparation_join [`sn`,`sm`] >>
  Cases_on `args_len = Lit 0w` >> gvs[] >>
  irule create_cut_code_join >> qexists_tac `se` >> simp[] >>
  preparation_join [`sx`]
QED

Theorem create_emit_and_check_cut[local]:
  (case salt of NONE => emit_op CREATE [value;buf;len]
    | SOME op => emit_op CREATE2 [value;buf;len;op]) sc = (created,sd) /\
  compile_check_create_result created rof sd = (result,sb) ==>
  create_cut_code {} sc sb
Proof
  strip_tac >> irule create_cut_code_join >> qexists_tac `sd` >> conj_tac
  >- (Cases_on `salt` >> fs[] >> preparation_step)
  >> metis_tac[create_result_check_cut_code, pairTheory.SND]
QED

Theorem create_create_call_cut_code:
  (!ce ty e a. create_cut_code {} a (SND (cfn ce ty e a))) ==>
  create_cut_code {} a (SND (compile_create_call cfn cenv ck has_salt rof args a))
Proof
  strip_tac >> irule create_create_call_case >>
  simp[create_bytecode_snapshot_cut_code, create_vv_snapshot_cut_code,
       create_encode_values_cut_code, create_result_check_cut_code,
       cj 4 create_fixed_preparation_intervals] >>
  `!ce ty e a. create_cut_code {} a (SND (lower_value cfn ce ty e a))` by
    (simp[lower_value_def] >> rpt gen_tac >> irule create_preparation_segments_case >>
     simp[create_unwrap_cut_code]) >>
  simp[] >> rpt conj_tac
  >- (rpt gen_tac >> Cases_on `salt` >> simp[compile_create_salt_def] >>
      irule create_preparation_segments_case >> simp[])
  >- (rpt gen_tac >> Cases_on `compile_create_copy target value salt rof a` >>
      drule create_copy_create_prefix >> strip_tac >> simp[] >>
      irule create_cut_code_join >> qexists_tac `sc` >> conj_tac
      >- (irule (cj 5 create_preparation_cut_code) >> simp[] >>
          rpt (goal_assum (drule_at Any)))
      >> metis_tac[create_emit_and_check_cut])
  >> rpt gen_tac >>
  Cases_on `compile_create_blueprint_append target value salt offset code args_ptr args_len rof a` >>
  drule create_blueprint_create_prefix >> strip_tac >> simp[] >>
  irule create_cut_code_join >> qexists_tac `sc` >> conj_tac
  >- (irule (cj 6 create_preparation_cut_code) >> simp[] >>
      rpt (goal_assum (drule_at Any)))
  >> metis_tac[create_emit_and_check_cut]
QED
