(* Static identification of the outer CREATE, independent of execution. *)
Theory createSizeDispatch
Ancestors
  builtinCreate exprLowering exprLoweringProps dallocaCreateGeometry compilerInstructionSuffix
  loweringShapeDefs loweringShapeRules fragExec fragFuel abiEncoderProps localPtrsProps
  emitHelper context compileEnv venomInst venomExecSemantics venomExecProps venomWf
  deadStoreElimStructure list rich_list

Theorem create_check_result_suffix[local]:
  compile_check_create_result created rof sd = (result,sb) ==>
  ci_mono sd sb /\
  EVERY (\i. ~MEM i.inst_opcode [CREATE;CREATE2]) (added_insts sd sb) /\
  (!id. id IN frag_ids sd sb ==>
    ?i. MEM i (added_insts sd sb) /\ i.inst_id = id)
Proof
  Cases_on `rof` >>
  simp[compile_check_create_result_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, ci_mono_refl, added_insts_def, frag_ids_def,
       fresh_label_def, emit_inst_def, new_block_def, emit_op_def,
       emit_void_def, compile_alloc_buffer_def, fresh_id_def, fresh_var_def,
       emit_def] >>
  strip_tac >> gvs[ci_mono_def, cs_extends_def, state_insts_def, all_blocks_def,
       MAP_APPEND, FLAT_APPEND, mk_inst_def] >>
  `!a b. a + b - (a + (b + 1)) = 0` by decide_tac >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
  simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> decide_tac
QED

(* The split includes the instruction as well as the cut preceding it. *)
Theorem create_size_identify_emit:
  ci_mono sa sc /\
  emit_op opc ops sc = (created,sd) /\
  MEM opc [CREATE;CREATE2] /\
  compile_check_create_result created rof sd = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids sa sb /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
       MEM j.inst_opcode [CREATE;CREATE2] ==> j.inst_id <= inst.inst_id) ==>
  ?out bb. created = Var out /\ inst = mk_inst sc.cs_next_id opc ops [out] /\
    lookup_block sc.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sc.cs_current_insts) = SOME inst
Proof
  strip_tac >>
  drule added_insts_emit_op >> strip_tac >>
  drule create_check_result_suffix >> strip_tac >>
  `cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd sb /\
   sc.cs_next_id IN frag_ids sa sb` by gvs[ci_mono_def, frag_ids_def] >>
  `fn_has_code sc sd func` by metis_tac[fn_has_code_mid] >>
  `fn_has_code sd sb func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  `~(inst.inst_id IN frag_ids sd sb)` by
    (strip_tac >>
     `~MEM inst.inst_opcode [CREATE;CREATE2]` suffices_by simp[] >>
     irule (BETA_RULE (Q.INST [`P` |-> `\i. ~MEM i.inst_opcode [CREATE;CREATE2]`]
       added_insts_function_property)) >>
     qexistsl_tac [`func`,`sd`,`sb`] >> simp[]) >>
  qabbrev_tac `i = mk_inst sc.cs_next_id opc ops [q]` >>
  `MEM i (fn_insts func)` by
    (irule added_insts_function_member >> qexistsl_tac [`sc`,`sd`] >> simp[Abbr `i`]) >>
  `i.inst_id = sc.cs_next_id /\ i.inst_opcode = opc` by simp[Abbr `i`, mk_inst_def] >>
  `i.inst_id <= inst.inst_id` by metis_tac[] >>
  `i.inst_id = inst.inst_id` by gvs[frag_ids_def] >>
  `i = inst` by metis_tac[fn_inst_ids_distinct_inj] >>
  qpat_x_assum `emit_op _ _ _ = _` (strip_assume_tac o MATCH_MP emit_op_facts) >>
  qpat_x_assum `fn_has_code sc sd func`
    (strip_assume_tac o REWRITE_RULE[fn_has_code_def]) >>
  gvs[IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN, Abbr `i`]
QED

(* Retain the precise producer of the size for the two external-code forms. *)
Definition create_size_dispatch_tail_def:
  create_size_dispatch_tail rof sc sd created bufop len value salt result sb <=>
    (case salt of NONE => emit_op CREATE [value;bufop;len]
     | SOME x => emit_op CREATE2 [value;bufop;len;x]) sc = (created,sd) /\
    compile_check_create_result created rof sd = (result,sb)
End

Definition create_size_dispatch_reaches_def[local]:
  create_size_dispatch_reaches P rof sa result sb <=>
    ?sc sd created bufop len value salt.
      ci_mono sa sc /\ P bufop len sc /\
      create_size_dispatch_tail rof sc sd created bufop len value salt result sb
End

Theorem dispatch_reaches_bind[local]:
  (!sa. ci_mono sa (SND (m sa))) /\
  (!v sa. create_size_dispatch_reaches P rof sa (FST (k v sa)) (SND (k v sa))) ==>
  !sa. create_size_dispatch_reaches P rof sa
    (FST (comp_bind m k sa)) (SND (comp_bind m k sa))
Proof
  strip_tac >> gen_tac >> Cases_on `m sa` >>
  gvs[comp_bind_def, create_size_dispatch_reaches_def] >>
  first_x_assum (qspecl_then [`q`,`r`] strip_assume_tac) >>
  `ci_mono sa r` by metis_tac[pairTheory.SND] >> metis_tac[ci_mono_trans]
QED

Theorem dispatch_reaches_builtin[local]:
  P bufop len sa ==>
  create_size_dispatch_reaches P rof sa
    (FST (compile_create_dispatch bufop len value salt rof sa))
    (SND (compile_create_dispatch bufop len value salt rof sa))
Proof
  Cases_on `salt` >>
  simp[compile_create_dispatch_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> simp[create_size_dispatch_reaches_def] >>
  irule_at Any ci_mono_refl >> simp[create_size_dispatch_tail_def] >>
  qexistsl_tac [`value`,`cs'`] >>
  (qpat_assum `emit_op CREATE _ _ = _` (K (qexists_tac `NONE`)) ORELSE
   (rename1 `emit_op CREATE2 [value;bufop;len;saltop] sa = _` >>
    qexists_tac `SOME saltop`)) >>
  qexistsl_tac [`len`,`result`,`bufop`] >> simp[]
QED

Theorem dispatch_mono_pairs[local]:
  (emit_op opc ops a = (op,b) ==> ci_mono a b) /\
  (emit_void opc ops a = (v,b) ==> ci_mono a b) /\
  (compile_alloc_dynamic sz a = (op,b) ==> ci_mono a b) /\
  (compile_copy_memory_dynamic dest src len a = (v,b) ==> ci_mono a b)
Proof
  simp[compile_alloc_dynamic_def] >> rpt conj_tac >> strip_tac
  >- metis_tac[ci_mono_emit_op, pairTheory.SND]
  >- metis_tac[ci_mono_emit_void, pairTheory.SND]
  >- metis_tac[ci_mono_emit_op, pairTheory.SND]
  >- metis_tac[ci_mono_compile_copy_memory_dynamic, pairTheory.SND]
QED

val dispatch_mono_tac = FIRST (map (fn th =>
  irule th >> goal_assum (drule_at Any) >> NO_TAC)
  (CONJUNCTS dispatch_mono_pairs));

Theorem dispatch_reaches_copy[local]:
  create_size_dispatch_reaches
    (\bufop len sc. ?code a1 a10.
       emit_op EXTCODESIZE [target] sa = (code,a1) /\
       emit_op ADD [code;Lit 11w] a10 = (len,sc)) rof sa
    (FST (compile_create_copy target value salt rof sa))
    (SND (compile_create_copy target value salt rof sa))
Proof
  Cases_on `compile_create_copy target value salt rof sa` >>
  drule create_copy_create_prefix >> strip_tac >>
  `ci_mono sa sc` by
    (map_every (fn cut => irule ci_mono_trans >> qexists_tac cut >>
       (reverse conj_tac >- dispatch_mono_tac))
       [`a10`,`a9`,`a8`,`a7`,`a6`,`a5`,`a4`,`a3`,`a2`,`a1`] >> dispatch_mono_tac) >>
  simp[create_size_dispatch_reaches_def, create_size_dispatch_tail_def] >>
  rpt (goal_assum $ drule_at Any)
QED

Theorem dispatch_reaches_blueprint[local]:
  create_size_dispatch_reaches
    (\bufop len sc. ?sm. emit_op ADD [code;args_len] sa = (len,sm)) rof sa
    (FST (compile_create_blueprint_append target value salt offs code args_ptr args_len rof sa))
    (SND (compile_create_blueprint_append target value salt offs code args_ptr args_len rof sa))
Proof
  Cases_on `compile_create_blueprint_append target value salt offs code args_ptr args_len rof sa` >>
  drule create_blueprint_create_prefix >> strip_tac >>
  `ci_mono sa se` by
    (map_every (fn cut => irule ci_mono_trans >> qexists_tac cut >>
       (reverse conj_tac >- dispatch_mono_tac)) [`sn`,`sm`] >> dispatch_mono_tac) >>
  `ci_mono sa sc` by
    (Cases_on `args_len = Lit 0w` >> gvs[] >>
     irule ci_mono_trans >> qexists_tac `se` >> simp[] >>
     irule ci_mono_trans >> qexists_tac `sx` >> conj_tac >> dispatch_mono_tac) >>
  simp[create_size_dispatch_reaches_def, create_size_dispatch_tail_def] >>
  rpt (goal_assum $ drule_at Any)
QED

(* Weakening the producer assertion leaves the selected dispatch unchanged. *)
Theorem dispatch_reaches_weaken[local]:
  (!bufop len sc. P bufop len sc ==> Q bufop len sc) /\
  create_size_dispatch_reaches P rof sa result sb ==>
  create_size_dispatch_reaches Q rof sa result sb
Proof
  rw[create_size_dispatch_reaches_def] >> metis_tac[]
QED

val dispatch_bind_tac = match_mp_tac (SPEC_ALL dispatch_reaches_bind) >>
  conj_tac >- simp[ci_mono_lower_value_cfn, ci_mono_emit_op,
    ci_mono_compile_create_snapshot, ci_mono_compile_create_salt,
    ci_mono_compile_create_proxy_buf, ci_mono_compile_create_blueprint_check,
    ci_mono_compile_create_blueprint_args] >>
  rpt gen_tac >> BETA_TAC;

Theorem dispatch_raw_prep_mono[local]:
  (!ce ty e sa. ci_mono sa (SND (cfn ce ty e sa))) ==>
  ci_mono sa (SND ((if args = [] then comp_return (data,len) else
    comp_bind (compile_create_ctor_args cfn cenv args) (\vals.
    comp_bind (compile_alloc_buffer n) (\buf.
    comp_ignore_bind (compile_copy_memory_dynamic buf.buf_operand data len)
      (comp_bind (emit_op ADD [buf.buf_operand;len]) (\dest.
      comp_bind (compile_abi_encode_values_to_buf cenv dest (ZIP (vals,tys))) (\args_len.
      comp_bind (emit_op ADD [len;args_len]) (\total.
      comp_return (buf.buf_operand,total)))))))) sa))
Proof
  strip_tac >> IF_CASES_TAC >> simp[ci_mono_comp_return] >>
  rpt (FIRST [ho_match_mp_tac ci_mono_bind, ho_match_mp_tac ci_mono_ignore_bind] >>
       conj_tac >- simp[ci_mono_compile_create_ctor_args, ci_mono_compile_alloc_buffer,
         ci_mono_compile_copy_memory_dynamic, ci_mono_compile_abi_encode_values_to_buf,
         ci_mono_emit_op] >> rpt gen_tac >> BETA_TAC) >> simp[ci_mono_comp_return]
QED

Theorem dispatch_reaches_raw[local]:
  (!ce ty e sa. ci_mono sa (SND (cfn ce ty e sa))) ==>
  create_size_dispatch_reaches (\bufop len sc. T) rof sa
    (FST (compile_raw_create cfn cenv bytes vexp args salted rof sa))
    (SND (compile_raw_create cfn cenv bytes vexp args salted rof sa))
Proof
  strip_tac >> simp_tac (srw_ss()) [compile_raw_create_def, LET_THM] >>
  ntac 4 dispatch_bind_tac >>
  match_mp_tac (SPEC_ALL dispatch_reaches_bind) >> conj_tac
  >- simp[dispatch_raw_prep_mono] >>
  qx_gen_tac `p` >> PairCases_on `p` >> simp_tac (srw_ss()) [] >>
  ntac 2 dispatch_bind_tac >> match_mp_tac (SPEC_ALL dispatch_reaches_builtin) >> simp[]
QED

Theorem dispatch_reaches_create_call[local]:
  (!ce ty e sa. ci_mono sa (SND (cfn ce ty e sa))) /\
  compile_create_call cfn cenv ck salted rof args sa = (result,sb) ==>
  (result = Lit 0w /\ emit_inst INVALID [] [] sa = ((),sb)) \/
  create_size_dispatch_reaches (\bufop len sc. ck = CreateMinimalProxy ==> len = Lit 54w)
    rof sa result sb
Proof
  strip_tac >>
  qpat_x_assum `compile_create_call _ _ _ _ _ _ _ = _`
    (fn th => pure_once_rewrite_tac
      (map (SYM o REWRITE_RULE [pairTheory.FST, pairTheory.SND])
           [Q.AP_TERM `FST` th, Q.AP_TERM `SND` th])) >>
  Cases_on `args` >>
  simp_tac (srw_ss()) [compile_create_call_def, LET_THM]
  >- (disj1_tac >> Cases_on `emit_inst INVALID [] [] sa` >>
      Cases_on `q` >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  Cases_on `t` >> simp_tac (srw_ss()) []
  >- (disj1_tac >> Cases_on `emit_inst INVALID [] [] sa` >>
      Cases_on `q` >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  IF_CASES_TAC >> simp_tac (srw_ss()) []
  >- (disj1_tac >> Cases_on `emit_inst INVALID [] [] sa` >>
      Cases_on `q` >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  disj2_tac >> Cases_on `ck` >> simp_tac (srw_ss()) [LET_THM]
  >- (ntac 4 dispatch_bind_tac >>
      match_mp_tac (SPEC_ALL dispatch_reaches_builtin) >> simp[])
  >- (ntac 3 dispatch_bind_tac >> irule dispatch_reaches_weaken >>
      irule_at Any dispatch_reaches_copy >> simp[])
  >- (ntac 2 dispatch_bind_tac >>
      rename1 `create_size_dispatch_reaches _ _ _ (FST (_ (payload:operand # operand) _)) _` >>
      PairCases_on `payload` >> simp_tac (srw_ss()) [] >>
      ntac 2 dispatch_bind_tac >>
      match_mp_tac (SPEC_ALL dispatch_reaches_bind) >> conj_tac
      >- (rpt gen_tac >> rpt CASE_TAC >> simp[ci_mono_comp_return, ci_mono_lower_value_cfn]) >>
      rpt gen_tac >> BETA_TAC >> dispatch_bind_tac >>
      irule dispatch_reaches_weaken >> irule_at Any dispatch_reaches_blueprint >> simp[]) >>
  match_mp_tac (SPEC_ALL dispatch_reaches_raw) >> simp[]
QED

Theorem create_dispatch_pc_unique:
  fn_inst_ids_distinct func /\
  lookup_block l1 func.fn_blocks = SOME bb1 /\ get_instruction bb1 i = SOME inst /\
  lookup_block l2 func.fn_blocks = SOME bb2 /\ get_instruction bb2 j = SOME inst ==>
  l1 = l2 /\ i = j
Proof
  strip_tac >>
  `MEM bb1 func.fn_blocks /\ MEM bb2 func.fn_blocks /\
   bb1.bb_label = l1 /\ bb2.bb_label = l2` by metis_tac[lookup_block_MEM, lookup_block_label] >>
  `bb1 = bb2 /\ i = j` suffices_by metis_tac[] >>
  irule (flat_map_occurrence_unique |> Q.GEN `f` |>
    Q.ISPEC `(\inst. inst.inst_id)` |> Q.GEN `g` |>
    Q.ISPEC `(\b. b.bb_instructions)`) >>
  gvs[get_instruction_def, AllCaseEqs()] >>
  qexists_tac `func.fn_blocks` >> fs[fn_inst_ids_distinct_def, combinTheory.o_DEF]
QED

Theorem create_size_dispatch_identification:
  (!ce ty e st. ci_mono st (SND (cfn ce ty e st))) /\
  compile_create_call cfn cenv ck salted rof args sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  lookup_block lbl func.fn_blocks = SOME bb /\ get_instruction bb idx = SOME inst /\
  inst.inst_id IN frag_ids sa sb /\ MEM inst.inst_opcode [CREATE;CREATE2] /\
  (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
       MEM j.inst_opcode [CREATE;CREATE2] ==> j.inst_id <= inst.inst_id) ==>
  ?sc sd created bufop len value salt out cb.
    ci_mono sa sc /\
    create_size_dispatch_tail rof sc sd created bufop len value salt result sb /\
    created = Var out /\
    inst = (case salt of
      NONE => mk_inst sc.cs_next_id CREATE [value;bufop;len] [out]
    | SOME x => mk_inst sc.cs_next_id CREATE2 [value;bufop;len;x] [out]) /\
    lookup_block sc.cs_current_bb func.fn_blocks = SOME cb /\
    get_instruction cb (LENGTH sc.cs_current_insts) = SOME inst /\
    lbl = sc.cs_current_bb /\ idx = LENGTH sc.cs_current_insts /\
    (ck = CreateMinimalProxy ==> len = Lit 54w)
Proof
  strip_tac >> drule_all lookup_block_get_instruction_fn_insts >> strip_tac >>
  drule_all dispatch_reaches_create_call >> strip_tac
  >- (drule added_insts_emit_inst >> strip_tac >>
      `~MEM inst.inst_opcode [CREATE;CREATE2]` suffices_by simp[] >>
      irule (BETA_RULE (Q.INST [`P` |-> `\i. ~MEM i.inst_opcode [CREATE;CREATE2]`]
        added_insts_function_property)) >>
      qexistsl_tac [`func`,`sa`,`sb`] >>
      fs[mk_inst_def, ci_mono_def, frag_ids_def]) >>
  qpat_x_assum `create_size_dispatch_reaches _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[create_size_dispatch_reaches_def]) >>
  `MEM CREATE [CREATE;CREATE2] /\ MEM CREATE2 [CREATE;CREATE2]` by simp[] >>
  Cases_on `salt` >>
  qpat_x_assum `create_size_dispatch_tail _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [create_size_dispatch_tail_def]) >>
  drule_all create_size_identify_emit >> strip_tac >>
  qexistsl_tac [`sc`,`sd`,`created`,`bufop`,`len`,`value`] >>
  (qpat_assum `emit_op CREATE _ _ = _` (K (qexists_tac `NONE`)) ORELSE
   (rename1 `emit_op CREATE2 [value;bufop;len;saltop] sc = _` >> qexists_tac `SOME saltop`)) >>
  rename1 `lookup_block sc.cs_current_bb func.fn_blocks = SOME cutbb` >>
  `lbl = sc.cs_current_bb /\ idx = LENGTH sc.cs_current_insts` by
    metis_tac[create_dispatch_pc_unique] >>
  qexistsl_tac [`out`,`cutbb`] >> fs[create_size_dispatch_tail_def]
QED
