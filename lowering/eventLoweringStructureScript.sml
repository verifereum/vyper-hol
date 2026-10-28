(* TOP-LEVEL: structural certificates for the actual LOG compiler and helpers.
   Arguments are compiled in source order and retain their source layout types.
   These certificates do not assume expression execution or payload framing. *)
Theory eventLoweringStructure
Ancestors
  stmtLowering exprLowering exprLoweringProps compileEnv context list rich_list

Theorem compile_log_save_arg_identity:
  !cenv src_ty op args cs.
    is_word_type src_ty \/ EVERY pure_expr args ==>
    compile_log_save_arg cenv src_ty op args cs = (op,cs)
Proof
  simp[compile_log_save_arg_def, comp_return_def]
QED

Theorem compile_log_save_arg_ci_mono:
  !cenv src_ty op args cs.
    ci_mono cs (SND (compile_log_save_arg cenv src_ty op args cs))
Proof
  rpt gen_tac >> simp[compile_log_save_arg_def] >>
  IF_CASES_TAC >> simp[ci_mono_comp_return, ci_mono_compile_materialize_vv]
QED

Theorem compile_log_eval_all_ci_mono:
  !cenv args cs.
    ci_mono cs (SND (compile_log_eval_all cenv args cs))
Proof
  Induct_on `args` >> rpt gen_tac >>
  simp_tac (srw_ss()) [Once compile_log_eval_all_def, LET_THM,
    ci_mono_comp_return] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_lower_value_compile_expr] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >>
  conj_tac >- simp[compile_log_save_arg_ci_mono] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >>
  simp[ci_mono_comp_return]
QED

Theorem compile_log_eval_all_types:
  !cenv args cs.
    MAP SND (FST (compile_log_eval_all cenv args cs)) =
    MAP (lowered_value_type cenv) args
Proof
  Induct_on `args` >>
  simp[compile_log_eval_all_def, comp_bind_def, comp_return_def,
    LET_THM, pairTheory.UNCURRY]
QED

Theorem compile_log_eval_all_length:
  !cenv args cs.
    LENGTH (FST (compile_log_eval_all cenv args cs)) = LENGTH args
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`cenv`, `args`, `cs`] compile_log_eval_all_types) >>
  disch_then (mp_tac o AP_TERM ``LENGTH : type list -> num``) >> simp[]
QED

(* A pure suffix cannot introduce additional snapshots into the prefix. *)
Theorem compile_log_eval_all_append:
  !cenv prefix suffix cs.
    EVERY pure_expr suffix ==>
    compile_log_eval_all cenv (prefix ++ suffix) cs =
    (let (left,mid) = compile_log_eval_all cenv prefix cs in
     let (right,final) = compile_log_eval_all cenv suffix mid in
     (left ++ right,final))
Proof
  Induct_on `prefix` >> rpt strip_tac >>
  simp[compile_log_eval_all_def, comp_bind_def, comp_return_def,
    compile_log_save_arg_def, EVERY_APPEND, LET_THM, pairTheory.UNCURRY]
QED

Theorem compile_log_eval_all_extends_insts:
  !cenv args cs ops cs'.
    compile_log_eval_all cenv args cs = (ops,cs') /\ same_blocks cs cs' ==>
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs'
Proof
  rpt strip_tac >>
  `ci_mono cs cs'` by
    (mp_tac (Q.SPECL [`cenv`, `args`, `cs`] compile_log_eval_all_ci_mono) >>
     simp[]) >>
  `isPREFIX cs.cs_current_insts cs'.cs_current_insts` by
    gvs[ci_mono_def, same_blocks_def] >>
  gvs[GSYM prefix_drop_equiv, emitted_insts_def]
QED

(* Monotonicity composes through each compiler bind; the operation lemmas
   also cover copies and ABI encoders that create additional blocks. *)
val log_structure_rules =
  [ci_mono_comp_return, ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst,
   ci_mono_compile_alloc_buffer, ci_mono_compile_store_memory,
   ci_mono_compile_abi_encode, compile_log_eval_all_ci_mono];

fun log_structure_tac rules =
  rpt (FIRST
    [CHANGED_TAC (asm_simp_tac (srw_ss()) rules),
     ho_match_mp_tac ci_mono_bind >> conj_tac >> rpt gen_tac,
     ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >> rpt gen_tac,
     IF_CASES_TAC]);

Theorem compile_encode_log_topic_ci_mono:
  !op is_bytes cs.
    ci_mono cs (SND (compile_encode_log_topic op is_bytes cs))
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_encode_log_topic_def] >>
  log_structure_tac log_structure_rules
QED

Theorem compile_log_topic_ops_ci_mono:
  !topics cs. ci_mono cs (SND (compile_log_topic_ops topics cs))
Proof
  Induct_on `topics` >> rpt gen_tac >>
  simp_tac (srw_ss()) [Once compile_log_topic_ops_def] >>
  log_structure_tac (compile_encode_log_topic_ci_mono :: log_structure_rules)
QED

Theorem compile_log_store_data_ci_mono:
  !cenv ops types buf offset cs.
    ci_mono cs (SND (compile_log_store_data cenv ops types buf offset cs))
Proof
  Induct_on `ops` >> Cases_on `types` >> rpt gen_tac >>
  simp_tac (srw_ss()) [Once compile_log_store_data_def, LET_THM] >>
  log_structure_tac log_structure_rules
QED

Theorem compile_log_store_data_cons:
  !cenv x xs ty tys buf offset.
    compile_log_store_data cenv (x::xs) (ty::tys) buf offset =
    comp_ignore_bind (compile_log_store_data cenv [x] [ty] buf offset)
      (compile_log_store_data cenv xs tys buf (offset + type_memory_bytes cenv ty))
Proof
  rpt gen_tac >>
  simp[compile_log_store_data_def, comp_ignore_bind_def, comp_bind_def,
    comp_return_def, FUN_EQ_THM, LET_THM, pairTheory.UNCURRY]
QED

Theorem compile_log_store_data_split:
  !cenv x xs ty tys buf offset cs ret cs'.
    compile_log_store_data cenv (x::xs) (ty::tys) buf offset cs = (ret,cs') <=>
    ?mid. compile_log_store_data cenv [x] [ty] buf offset cs = ((),mid) /\
      compile_log_store_data cenv xs tys buf
        (offset + type_memory_bytes cenv ty) mid = (ret,cs')
Proof
  rpt gen_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_log_store_data_cons])) >>
  Cases_on `compile_log_store_data cenv [x] [ty] buf offset cs` >>
  rename1 `compile_log_store_data cenv [x] [ty] buf offset cs = (field_ret,mid)` >>
  Cases_on `field_ret` >> simp[comp_ignore_bind_def, comp_bind_def]
QED

Theorem compile_log_stmt_ci_mono:
  !cenv lctx ty event_id args cs.
    ci_mono cs (SND (compile_stmt cenv lctx ty (Log event_id args) cs))
Proof
  rpt gen_tac >>
  Cases_on `cenv.ce_event_info (nsid_to_string event_id)`
  >- simp[Once compile_stmt_def, LET_THM, ci_mono_emit_inst] >>
  rename1 `cenv.ce_event_info (nsid_to_string event_id) = SOME info` >>
  PairCases_on `info` >>
  simp_tac (srw_ss()) [Once compile_stmt_def, LET_THM] >>
  log_structure_tac (compile_log_topic_ops_ci_mono ::
    compile_log_store_data_ci_mono :: log_structure_rules)
QED

Theorem compile_log_stmt_extends_insts:
  !cenv lctx ty event_id args cs cs'.
    compile_stmt cenv lctx ty (Log event_id args) cs = ((),cs') /\
    same_blocks cs cs' ==>
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs'
Proof
  rpt strip_tac >>
  `ci_mono cs cs'` by
    (mp_tac (Q.SPECL [`cenv`, `lctx`, `ty`, `event_id`, `args`, `cs`]
      compile_log_stmt_ci_mono) >> simp[]) >>
  `isPREFIX cs.cs_current_insts cs'.cs_current_insts` by
    gvs[ci_mono_def, same_blocks_def] >>
  gvs[GSYM prefix_drop_equiv, emitted_insts_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed LOG compiler structure theorem: " ^ name)
  end)
  (DB.thms "eventLoweringStructure")
