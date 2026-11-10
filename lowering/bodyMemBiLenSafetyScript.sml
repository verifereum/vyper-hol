(* Header-load safety for captured len operands, including empty payloads. *)
Theory bodyMemBiLenSafety
Ancestors
  exprSimLen exprSimSource exprSimProps exprSimHypsDefs exprSimDefs
  loweringPosts list fragExec exprSimHyps exprSimWordBuiltins exprBopLowering
  exprLowering exprLoweringProps builtinSimple emitHelper compileEnv loweringStateRelDefs
  accountsRelProps valueEncoding venomExecSemantics venomInst venomState
  vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeBuiltins vyperValue vyperTyping vyperStorage builtinProps
  vyperTypeInvariants context freshWrites loweringSlice emitHelperProps
  exprSimUnwrap exprSimCopy vyperTypeExprResult vyperTypeExprSoundness
  vyperExprNoControl gasContext gasOutcome gasSummary gasSummaryCompose
  gasExemptCert fragGasMode fragGasPath exprSimBopRestWordLoadSafety
  exprSimMemDefs words

Theorem len_sized_store_header:
  is_sized_type t /\ evaluate_type tenv t = SOME vt ==>
  32 <= val_store_size vt v /\ 32 <= type_memory_size vt /\ ~is_word_type t
Proof
  strip_tac >> drule sized_type_cases >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), type_memory_size_def, is_word_type_def] >>
  Cases_on `v` >> simp[val_store_size_def, type_memory_size_def]
QED

Theorem len_vv_memory_header_bound:
  vv_holds cenv cx t tv vv es s /\ vv_store_bound cx t lt es tv vv s /\
  is_sized_type t /\ evaluate_type (get_tenv cx) t = SOME vt /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
  ?w. eval_operand (vv_operand vv) s = SOME w /\
      w2n w + 32 <= s.vs_alloca_next
Proof
  strip_tac >>
  `!v. 32 <= val_store_size vt v /\ ~is_word_type t` by
    metis_tac[len_sized_store_header] >>
  Cases_on `vv` >>
  gvs[vv_location_def, vv_operand_def, vv_holds_def, expr_val_rel_def,
      vv_store_bound_def] >>
  first_x_assum (qspec_then `v` strip_assume_tac) >> decide_tac
QED

Theorem len_load_mem_ok:
  compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
    (case vv_location vv of SOME l => l | NONE => LocMemory) sm = (op,sb) /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  vv_store_bound cx (expr_type e) lt es' tv vv s /\
  is_sized_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME vt ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s /\
   vv_holds cenv cx (expr_type e) tv vv es' s` by fs[vv_post_def] >>
  `32 <= type_memory_size vt /\ ~is_word_type (expr_type e)` by
    metis_tac[len_sized_store_header] >>
  `(vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
    ?w. eval_operand (vv_operand vv) s = SOME w /\
        w2n w + 32 <= s.vs_alloca_next` by
    (strip_tac >> metis_tac[len_vv_memory_header_bound]) >>
  gvs[compile_builtin_len_def] >>
  Cases_on `vv`
  >- (gvs[vv_location_def] >>
      irule (Q.INST [`loc` |-> `LocMemory`] rest_word_ptr_load_mem_ok) >>
      simp[] >> fs[vv_operand_def] >> metis_tac[]) >>
  gvs[vv_location_def, vv_operand_def, vv_holds_def] >>
  Cases_on `p.ptr_location` >> gvs[]
  >- (irule (Q.INST [`loc` |-> `LocMemory`] rest_word_ptr_load_mem_ok) >>
      simp[] >> metis_tac[])
  >- (irule (Q.INST [`loc` |-> `LocStorage`] rest_word_ptr_load_mem_ok) >>
      simp[] >> metis_tac[])
  >- (irule (Q.INST [`loc` |-> `LocTransient`] rest_word_ptr_load_mem_ok) >>
      simp[] >> metis_tac[]) >>
  drule_all rest_word_immutable_region_bound >> strip_tac >>
  `(cenv.ce_is_ctor /\ cenv.ce_imm_alloca <> NONE ==>
    eval_operand (THE cenv.ce_imm_alloca) s = SOME 0w)` by
    (fs[stmt_state_rel_def, immutable_base_zero_def] >>
     Cases_on `cenv.ce_imm_alloca` >> gvs[]) >>
  irule (Q.INST [`loc` |-> `LocCode`, `ctor` |-> `cenv.ce_is_ctor`,
                  `imm` |-> `cenv.ce_imm_alloca`] rest_word_ptr_load_mem_ok) >>
  simp[] >> qexistsl [`w`, `p.ptr_operand`, `cenv`, `op`] >> simp[] >>
  Cases_on `cenv.ce_is_ctor` >> gvs[] >> decide_tac
QED

Theorem len_vv_not_calldata:
  vv_holds cenv cx t tv vv es s ==>
  (case vv_location vv of SOME l => l | NONE => LocMemory) <> LocCalldata
Proof
  Cases_on `vv` >> simp[vv_location_def, vv_holds_def] >>
  Cases_on `p.ptr_location` >> simp[]
QED
