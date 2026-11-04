(* Value-layout, local-frame and leaf-evaluation facts for simulations. *)
Theory exprSimProps
Ancestors
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec varsExt loweringSlice localPtrsProps venomMemDefs
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding valueEncodingProofs vyperTypeSystem
  venomExecSemantics venomInst venomState
  vyperLookupStorage vyperStorageBackend vyperEvalPreservesScopes

Definition val_store_size_def:
  val_store_size tv v =
    case v of
      BytesV bs =>
        (case tv of
           BaseTV (BytesT (Dynamic _)) => 32 + 32 * word_size (LENGTH bs)
         | _ => type_memory_size tv)
    | StringV str =>
        (case tv of
           BaseTV (StringT _) => 32 + 32 * word_size (LENGTH str)
         | _ => type_memory_size tv)
    | _ => type_memory_size tv
End

Theorem locals_kept_mem_tail:
  !cenv es s0 t u.
    locals_kept cenv es s0 t /\ u.vs_memory = t.vs_memory ==>
    locals_kept cenv es s0 u
Proof
  rw[locals_kept_def]
QED

Theorem locals_kept_refl[simp]:
  !cenv es s. locals_kept cenv es s s
Proof
  simp[locals_kept_def]
QED

Theorem locals_kept_mem:
  !cenv es s0 s. s.vs_memory = s0.vs_memory ==> locals_kept cenv es s0 s
Proof
  metis_tac[locals_kept_mem_tail, locals_kept_refl]
QED

Theorem locals_kept_inst_idx[simp]:
  !cenv es s0 s k.
    locals_kept cenv es s0 (s with vs_inst_idx := k) <=>
    locals_kept cenv es s0 s
Proof
  simp[locals_kept_def]
QED

Theorem locals_kept_regions_tail:
  !cenv es s0 s t.
    locals_kept cenv es s0 s /\
    (!n b sz. local_region cenv es.scopes s0 n b sz ==>
       mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) ==>
    locals_kept cenv es s0 t
Proof
  rw[locals_kept_def] >>
  qpat_x_assum `!n b sz. local_region _ _ _ n b sz ==> _` drule >>
  strip_tac >>
  drule (cj 1 valueEncodingProofsTheory.mem_bytes_at_agree_window) >>
  disch_then (qspecl_then [`off`, `len`] mp_tac) >>
  impl_tac >- decide_tac >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem locals_kept_regions:
  !cenv es s0 s.
    (!n b sz. local_region cenv es.scopes s0 n b sz ==>
       mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory) ==>
    locals_kept cenv es s0 s
Proof
  metis_tac[locals_kept_regions_tail, locals_kept_refl]
QED

Theorem expr_val_at_start_mono:
  sa.cs_next_id <= s1.cs_next_id /\
  expr_val_at cenv cx ty s1 sm es v p s ==>
  expr_val_at cenv cx ty sa sm es v p s
Proof
  simp[expr_val_at_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> qexists_tac `w` >> simp[]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]
QED

Theorem expr_val_rel_mem_agree:
  !cx t v op s s' w tv.
    expr_val_rel cx t v op s /\ ~is_word_type t /\
    eval_operand op s = SOME w /\ eval_operand op s' = SOME w /\
    evaluate_type (get_tenv cx) t = SOME tv /\ val_wf tv v /\
    mem_bytes_at (w2n w) (type_memory_size tv) s.vs_memory =
      mem_bytes_at (w2n w) (type_memory_size tv) s'.vs_memory ==>
    expr_val_rel cx t v op s'
Proof
  rw[expr_val_rel_def] >> gvs[] >>
  qspecl_then [`tv`, `v`, `w2n w`, `type_memory_size tv`, `s.vs_memory`,
               `s'.vs_memory`] mp_tac
    valueEncodingPropsTheory.val_in_memory_mem_agree >>
  asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem le_word_size_mul:
  !n. n <= 32 * word_size n
Proof
  rw[vfmConstantsTheory.word_size_def] >>
  `(n + 31) MOD 32 < 32` by simp[] >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `n + 31` strip_assume_tac) >> decide_tac
QED

Theorem buffer_round_mask:
  !w:bytes32. w && i2w (- &32) = (w >>> 5) << 5
Proof
  `i2w (- &32):bytes32 = (-1w:bytes32) << 5` by
    (simp[integer_wordTheory.i2w_def] >> CONV_TAC wordsLib.WORD_EVAL_CONV) >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  simp_tac (bool_ss ++ fcpLib.FCP_ss)
    [wordsTheory.word_and_def, wordsTheory.word_lsl_def,
     wordsTheory.word_lsr_def, wordsTheory.WORD_NEG_1, wordsTheory.word_T] >>
  rpt strip_tac >> Cases_on `5 <= i` >>
  asm_simp_tac (arith_ss ++ fcpLib.FCP_ss) [wordsTheory.WORD_NEG_1, wordsTheory.word_T]
QED

Theorem word_size_le_of_le_mul[local]:
  !len k. len <= 32 * k ==> word_size len <= k
Proof
  rw[vfmConstantsTheory.word_size_def] >>
  `(32 * k + 31) DIV 32 = k` by
    (once_rewrite_tac[arithmeticTheory.MULT_COMM] >>
     irule arithmeticTheory.DIV_MULT >> simp[]) >>
  `(len + 31) DIV 32 <= (32 * k + 31) DIV 32` by
    (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >>
  gvs[]
QED

Theorem val_size_cases[local]:
  !tv v.
    (?bs n. v = BytesV bs /\ tv = BaseTV (BytesT (Dynamic n))) \/
    (?str n. v = StringV str /\ tv = BaseTV (StringT n)) \/
    (val_footprint tv v = type_memory_size tv /\
     val_store_size tv v = type_memory_size tv)
Proof
  rpt gen_tac >> Cases_on `v` >> simp[val_footprint_def, val_store_size_def] >>
  Cases_on `tv` >> simp[] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> simp[] >>
  rename1 `BytesT sz` >> Cases_on `sz` >> simp[]
QED

Theorem val_footprint_le:
  !tv v. val_wf tv v ==> val_footprint tv v <= type_memory_size tv
Proof
  rpt strip_tac >>
  `(?bs n. v = BytesV bs /\ tv = BaseTV (BytesT (Dynamic n))) \/
   (?str n. v = StringV str /\ tv = BaseTV (StringT n)) \/
   val_footprint tv v = type_memory_size tv` by
    metis_tac[val_size_cases]
  >- (gvs[val_footprint_def, valueEncodingTheory.val_wf_def,
          valueEncodingTheory.type_memory_size_def] >>
      qspec_then `n` mp_tac le_word_size_mul >> decide_tac)
  >- (gvs[val_footprint_def, valueEncodingTheory.val_wf_def,
          valueEncodingTheory.type_memory_size_def] >>
      qspec_then `n` mp_tac le_word_size_mul >> decide_tac) >>
  simp[]
QED

Theorem val_footprint_le_store_size:
  !tv v. val_footprint tv v <= val_store_size tv v
Proof
  rpt gen_tac >>
  qspecl_then [`tv`, `v`] strip_assume_tac val_size_cases >>
  gvs[val_footprint_def, val_store_size_def, le_word_size_mul]
QED

Theorem val_store_size_le:
  !tv v. val_wf tv v ==> val_store_size tv v <= type_memory_size tv
Proof
  rpt strip_tac >>
  `(?bs n. v = BytesV bs /\ tv = BaseTV (BytesT (Dynamic n))) \/
   (?str n. v = StringV str /\ tv = BaseTV (StringT n)) \/
   val_store_size tv v = type_memory_size tv` by
    metis_tac[val_size_cases]
  >- (gvs[val_store_size_def, valueEncodingTheory.val_wf_def,
          valueEncodingTheory.type_memory_size_def] >>
      irule word_size_le_of_le_mul >> simp[])
  >- (gvs[val_store_size_def, valueEncodingTheory.val_wf_def,
          valueEncodingTheory.type_memory_size_def] >>
      irule word_size_le_of_le_mul >> simp[]) >>
  simp[]
QED

Theorem val_in_memory_footprint_agree:
  !tv v off mem mem'.
    val_in_memory tv v off mem /\ val_wf tv v /\
    mem_bytes_at off (val_footprint tv v) mem =
      mem_bytes_at off (val_footprint tv v) mem' ==>
    val_in_memory tv v off mem'
Proof
  rpt strip_tac >>
  `(?bs n. v = BytesV bs /\ tv = BaseTV (BytesT (Dynamic n))) \/
   (?str n. v = StringV str /\ tv = BaseTV (StringT n)) \/
   val_footprint tv v = type_memory_size tv` by
    metis_tac[val_size_cases]
  >- (gvs[val_footprint_def, val_in_memory_def] >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      strip_tac >>
      `mem_word_at off mem' = mem_word_at off mem` by
        (qpat_x_assum `!off2. _ ==> mem_word_at _ _ = _` irule >> simp[]) >>
      `mem_bytes_at (off + 32) (LENGTH bs) mem' =
       mem_bytes_at (off + 32) (LENGTH bs) mem` by
        (qpat_x_assum `!off2 len2. _ ==> mem_bytes_at _ _ _ = _` irule >>
         simp[]) >>
      simp[])
  >- (gvs[val_footprint_def, val_in_memory_def] >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      strip_tac >>
      `mem_word_at off mem' = mem_word_at off mem` by
        (qpat_x_assum `!off2. _ ==> mem_word_at _ _ = _` irule >> simp[]) >>
      `mem_bytes_at (off + 32) (LENGTH str) mem' =
       mem_bytes_at (off + 32) (LENGTH str) mem` by
        (qpat_x_assum `!off2 len2. _ ==> mem_bytes_at _ _ _ = _` irule >>
         simp[]) >>
      simp[]) >>
  qpat_x_assum `val_footprint _ _ = _` (fn th => fs[th]) >>
  qspecl_then [`tv`, `v`, `off`, `type_memory_size tv`, `mem`, `mem'`]
    mp_tac valueEncodingPropsTheory.val_in_memory_mem_agree >>
  asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem expr_val_rel_footprint_agree:
  !cx t v op s s' w tv.
    expr_val_rel cx t v op s /\ ~is_word_type t /\
    eval_operand op s = SOME w /\ eval_operand op s' = SOME w /\
    evaluate_type (get_tenv cx) t = SOME tv /\ val_wf tv v /\
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory =
      mem_bytes_at (w2n w) (val_footprint tv v) s'.vs_memory ==>
    expr_val_rel cx t v op s'
Proof
  rw[expr_val_rel_def] >> gvs[] >>
  irule val_in_memory_footprint_agree >> simp[] >>
  qexists_tac `s.vs_memory` >> simp[]
QED

Theorem stmt_state_rel_vars_frame:
  !func cenv cx es s V ctx.
    stmt_state_rel ctx func cenv cx es s /\
    (!name entry p sz.
       lookup_scopes name es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       lookup_var p (s with vs_vars := V) = lookup_var p s) ==>
    stmt_state_rel ctx func cenv cx es (s with vs_vars := V)
Proof
  rpt strip_tac >>
  `local_ptrs_rel func cenv es.scopes (s with vs_vars := V)` by
    (irule local_ptrs_rel_frame >> qexists_tac `s` >>
     fs[stmt_state_rel_def, state_rel_def] >> conj_tac
     >- metis_tac[] >>
     rpt strip_tac >> gvs[]) >>
  `alloca_inv (s with vs_vars := V)` by
    (irule alloca_inv_fields >> qexists_tac `s` >> fs[stmt_state_rel_def]) >>
  `alloca_room ctx func (s with vs_vars := V)` by
    (irule alloca_room_fields >> qexists_tac `s` >> fs[stmt_state_rel_def]) >>
  `immutable_alloca_sep func cenv cx es (s with vs_vars := V)` by
    (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
     fs[stmt_state_rel_def] >>
     rpt strip_tac >> qexists_tac `id` >>
     fs[local_region_def] >> metis_tac[]) >>
  fs[stmt_state_rel_def, state_rel_def,
     storage_rel_def, transient_rel_def,
     immutables_rel_def, logs_rel_def, contract_storage_def,
     contract_transient_def] >>
  metis_tac[]
QED

Theorem stmt_state_rel_vars_ext:
  !func cenv cx es t t' ctx.
    stmt_state_rel ctx func cenv cx es t /\ vars_ext t t' ==>
    stmt_state_rel ctx func cenv cx es t'
Proof
  rw[vars_ext_def] >>
  qpat_x_assum `t' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >>
  fs[lookup_var_def] >> metis_tac[SUBMAP_FLOOKUP_EQN]
QED

Theorem stmt_state_rel_drop_fresh:
  !func cenv cx es st s ctx.
    local_ptrs_reserved cenv st ==>
    (stmt_state_rel ctx func cenv cx es (drop_fresh st s) <=>
     stmt_state_rel ctx func cenv cx es s)
Proof
  rpt strip_tac >> eq_tac >> strip_tac
  >- (irule stmt_state_rel_vars_ext >> qexists_tac `drop_fresh st s` >>
      simp[vars_ext_drop_fresh]) >>
  simp[drop_fresh_def] >> irule stmt_state_rel_vars_frame >> simp[] >>
  rpt strip_tac >> simp[GSYM drop_fresh_def] >>
  irule lookup_var_drop_fresh >>
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem typed_val_to_w256_word_value:
  !tv v. word_value v ==> typed_val_to_w256 tv v = val_to_w256 v
Proof
  rw[word_value_def] >> Cases_on `tv` >> simp[typed_val_to_w256_def] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> simp[typed_val_to_w256_def]
QED

Theorem val_in_memory_word_type:
  !tenv t tvt v off mem.
    is_word_type t /\ evaluate_type tenv t = SOME tvt /\
    value_has_type tvt v /\ val_in_memory tvt v off mem ==>
    mem_word_at off mem = typed_val_to_w256 tvt v
Proof
  rpt strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, val_in_memory_def,
      typed_val_to_w256_def]
QED

Theorem eval_expr_env:
  !cx ann item es res es'.
    (do result <- eval_expr cx (Builtin ann (Env item) []); read_result cx result od) es = (res, es') /\
    expr_res_ok res /\ item <> PrevHash /\ item <> MsgGas ==>
    es' = es /\
    ?v. res = INL v /\
        evaluate_builtin cx es.accounts ann (Env item) [] [] = INL v
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(do result <- eval_expr _ _; read_result _ result od) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
       builtin_args_length_ok_def, read_result_def] >>
  simp[Once evaluate_def, bind_def, read_result_def, return_def] >>
  Cases_on `item` >> fs[evaluate_builtin_def, return_def, raise_def] >>
  rw[] >> gvs[expr_res_ok_def, read_result_def, return_def]
QED

Theorem lower_value_env:
  !cenv ty ann item sa op sb.
    lower_value compile_expr cenv ty (Builtin ann (Env item) []) sa =
      (op, sb) ==>
    compile_env_var item sa = (op, sb)
Proof
  rpt gen_tac >>
  simp[lower_value_def, compile_expr_def, comp_bind_def] >>
  Cases_on `compile_env_var item sa` >>
  simp[as_stack_val_def, unwrap_value_def, comp_return_def]
QED

Theorem eval_expr_flag_member:
  !cx ann src fid mid es res es'.
    (do result <- eval_expr cx (FlagMember ann (src, fid) mid); read_result cx result od) es = (res, es') /\
    expr_res_ok res ==>
    es' = es /\
    ?ts ls i. get_module_code cx src = SOME ts /\
              lookup_flag fid ts = SOME ls /\ INDEX_OF mid ls = SOME i /\
              res = INL (FlagV (2 ** i))
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, lookup_flag_mem_def] >>
  Cases_on `get_module_code cx src` >>
  gvs[bind_def, raise_def, return_def, expr_res_ok_def] >>
  rename1 `get_module_code cx src = SOME ts` >>
  Cases_on `lookup_flag fid ts` >>
  gvs[bind_def, raise_def, return_def, expr_res_ok_def] >>
  rename1 `lookup_flag fid ts = SOME ls` >>
  Cases_on `INDEX_OF mid ls` >>
  gvs[bind_def, read_result_def, raise_def, return_def, expr_res_ok_def]
QED

Theorem eval_expr_flag_member_gas:
  gas_admissible
    (bind (eval_expr cx (FlagMember ann (src,fid) mid)) (read_result cx))
    expr_res_ok es ==>
  ?ts ls i. get_module_code cx src = SOME ts /\
    lookup_flag fid ts = SOME ls /\ INDEX_OF mid ls = SOME i /\
    (!tail. bind (eval_expr cx (FlagMember ann (src,fid) mid))
       (read_result cx) (es with gas_obs := tail) =
       (INL (FlagV (2 ** i)), es with gas_obs := tail))
Proof
  strip_tac >>
  Cases_on `bind (eval_expr cx (FlagMember ann (src,fid) mid))
    (read_result cx) (es with gas_obs := [])` >>
  drule_all gasContextTheory.gas_admissible_result >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss() ++ ETA_ss) [] eval_expr_flag_member) >>
  strip_tac >>
  qexistsl [`ts`, `ls`, `i`] >> simp[] >>
  simp[Once evaluate_def, lookup_flag_mem_def, bind_def,
       read_result_def, return_def]
QED

(* Pointer variables and scope domains determine live local regions. *)
Theorem local_region_frame:
  !func cenv scopes0 s0 sa scopes t n b sz.
    local_ptrs_rel func cenv scopes0 s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM scopes0 = MAP FDOM scopes /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    local_region cenv scopes t n b sz ==>
    local_region cenv scopes0 s0 n b sz
Proof
  rw[local_region_def] >>
  `lookup_scopes n scopes0 <> NONE` by
    metis_tac[lookup_scopes_none_map_fdom, optionTheory.NOT_SOME_NONE] >>
  Cases_on `lookup_scopes n scopes0` >> fs[] >>
  rename1 `lookup_scopes n scopes0 = SOME e0` >>
  `?w0. lookup_var p s0 = SOME w0` by
    (fs[local_ptrs_rel_def] >>
     qpat_x_assum `!name entry p sz. _` drule_all >> metis_tac[]) >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `lookup_var p t = SOME w0` by metis_tac[] >> gvs[]
QED

(* The converse needs only preservation of pointers already present. *)
Theorem local_region_frame_fwd:
  !cenv scopes0 sa scopes s0 t n b sz.
    local_ptrs_reserved cenv sa /\ MAP FDOM scopes0 = MAP FDOM scopes /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    local_region cenv scopes0 s0 n b sz ==>
    local_region cenv scopes t n b sz
Proof
  rw[local_region_def] >>
  `lookup_scopes n scopes <> NONE` by
    metis_tac[lookup_scopes_none_map_fdom, optionTheory.NOT_SOME_NONE] >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  Cases_on `lookup_scopes n scopes` >> gvs[]
QED
