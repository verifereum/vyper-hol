(* Source bounds used by the memory-labelled concat head bridge. *)
Theory bodyMemBiConcatHead
Ancestors
  bodyMemBiConcatArms bodyMemBiConcatBounds exprSimMemDefs exprLoweringProps
  exprSimDefs exprSimProps exprSimConcatArgs exprOperandVar freshWrites
  loweringPosts exprLowering exprSimConcatStep exprSimConcatPath fragExec venomExecSemantics venomState compileEnv words arithmetic loweringStateRelDefs
Libs
  monadsyntax

Theorem concat_head_endpoint_frame_mem[local]:
  local_ptrs_reserved cenv s1 /\ local_ptrs_rel func cenv es1.scopes t /\
  not_fresh_at s1 dv /\ not_fresh_at s1 ov /\
  lookup_var dv t = SOME (n2w (B + 32)) /\ lookup_var ov t = SOME ow /\
  FLOOKUP t.vs_allocas binst.inst_id = SOME (B,bsz) /\
  FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
  (!name lb lsz. local_region cenv es1.scopes t name lb lsz ==>
    (B + bsz <= lb \/ lb + lsz <= B) /\
    (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
  t2.vs_allocas = t.vs_allocas /\
  (!z. not_fresh_at s1 z ==> lookup_var z t2 = lookup_var z t) ==>
  lookup_var dv t2 = SOME (n2w (B + 32)) /\ lookup_var ov t2 = SOME ow /\
  FLOOKUP t2.vs_allocas binst.inst_id = SOME (B,bsz) /\
  FLOOKUP t2.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
  (!name lb lsz. local_region cenv es1.scopes t2 name lb lsz ==>
    (B + bsz <= lb \/ lb + lsz <= B) /\
    (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow))
Proof
  strip_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `local_region cenv es1.scopes t name lb lsz` by
    (irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`s1`, `es1.scopes`, `t2`] >> simp[]) >>
  qpat_x_assum `!name lb lsz. local_region _ _ t _ _ _ ==> _` drule >> simp[]
QED

Theorem concat_head_arm_mem:
  !ctx func cenv cx e args es sa s1 sb s0 es1 v op t B bsz ow k P binst
   oinst dv ov tv.
    compile_concat compile_expr cenv (e::args) (Var dv) (MAP (\e. let ety = expr_type e in
                if is_bytestring_type ety then (T, 0:num)
                else case ety of
                       BaseT (BytesT (Fixed m)) => (F, m)
                     | _ => (F, 32:num)) (e::args))
      (Var ov) sa = ((), sb) /\
    lower_value compile_expr cenv (expr_type e) e sa = (op, s1) /\
    (is_bytestring_type (expr_type e) \/
     ?m. expr_type e = BaseT (BytesT (Fixed m))) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
    expr_post ctx func cenv cx e es sa s1 s0 es1 v op t /\
    ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    not_fresh_at sa dv /\ not_fresh_at sa ov /\
    lookup_var dv s0 = SOME (n2w (B + 32)) /\ lookup_var ov s0 = SOME ow /\
    MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
    binst.inst_id < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas binst.inst_id = SOME (B, bsz) /\
    MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
    oinst.inst_id < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas oinst.inst_id = SOME (w2n ow, 64) /\
    (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
       (B + bsz <= lb \/ lb + lsz <= B) /\
       (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
    (B + bsz <= w2n ow \/ w2n ow + 64 <= B) /\ B + bsz < dimword (:256) /\
    mload (w2n ow) s0 = n2w k /\ k <= P /\
    32 + P + SUM (MAP concat_payload_capacity (MAP expr_type (e::args))) <= bsz /\
    32 + concat_data_bound P (MAP expr_type (e::args)) <= bsz /\
    fn_inst_ids_distinct func /\ expr_store_bound cx (expr_type e) v op t /\
    alloca_history func t ==>
    ?s2 t2.
      compile_concat compile_expr cenv args (Var dv) (MAP (\e. let ety = expr_type e in
                if is_bytestring_type ety then (T, 0:num)
                else case ety of
                       BaseT (BytesT (Fixed m)) => (F, m)
                     | _ => (F, 32:num)) args)
        (Var ov) s2 = ((), sb) /\
      ci_mono sa s1 /\ ci_mono s1 s2 /\ fn_has_code s2 sb func /\
      gas_path_mem ctx func t 0 (OK t2) /\
      stmt_state_rel ctx func cenv cx es1 t2 /\ ~t2.vs_halted /\
      t2.vs_current_bb = s2.cs_current_bb /\
      t2.vs_inst_idx = LENGTH s2.cs_current_insts /\
      lookup_var dv t2 = SOME (n2w (B + 32)) /\ lookup_var ov t2 = SOME ow /\
      FLOOKUP t2.vs_allocas binst.inst_id = SOME (B, bsz) /\
      FLOOKUP t2.vs_allocas oinst.inst_id = SOME (w2n ow, 64) /\
      (!name lb lsz. local_region cenv es1.scopes t2 name lb lsz ==>
         (B + bsz <= lb \/ lb + lsz <= B) /\
         (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
      mload (w2n ow) t2 = n2w (k + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])) /\
      k + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) <= P + concat_payload_capacity (expr_type e) /\
      t2.vs_allocas = t.vs_allocas /\
      (!z. not_fresh_at s1 z ==> lookup_var z t2 = lookup_var z t) /\
      mem_bytes_at (B + 32) (k + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])) t2.vs_memory =
        mem_bytes_at (B + 32) k t.vs_memory ++ (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) /\
      (!p n. (p + n <= B \/ B + bsz <= p) /\
             (p + n <= w2n ow \/ w2n ow + 64 <= p) ==>
             mem_bytes_at p n t2.vs_memory = mem_bytes_at p n t.vs_memory) /\
      mem_bytes_at (B + 32) k t.vs_memory = mem_bytes_at (B + 32) k s0.vs_memory /\
      alloca_history func t2 /\ t2.vs_alloca_next = t.vs_alloca_next
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `ci_mono sa s1` by
    (drule (cj 2 compile_expr_grows) >> simp[ci_mono_def]) >>
  `sa.cs_next_var <= s1.cs_next_var /\ cs_extends sa s1` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. op = Var x ==> not_fresh_at s1 x` by
    metis_tac[compile_lower_value_var] >>
  `not_fresh_at s1 dv /\ not_fresh_at s1 ov` by metis_tac[not_fresh_at_mono] >>
  `32 + P + (concat_payload_capacity (expr_type e) +
     SUM (MAP concat_payload_capacity (MAP expr_type args))) <= bsz` by
    (qpat_x_assum `32 + P + SUM _ <= _` mp_tac >> simp[]) >>
  `32 + k <= bsz` by decide_tac >>
  drule_all concat_args_pre >> strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (qpat_assum `is_bytestring_type _ \/ _` strip_assume_tac
     >- (irule post_value_type_bytestring >> first_assum ACCEPT_TAC) >>
     irule post_value_type_word >>
     qpat_x_assum `evaluate_type _ (expr_type e) = SOME tv` mp_tac >>
     simp[vyperValueTheory.evaluate_type_def, is_word_type_def,
          optionTheory.IF_EQUALS_OPTION]) >>
  qpat_assum `post_value_type cenv e = _` (fn pth =>
    qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [expr_post_def, pth])) >>
  `mload (w2n ow) t = n2w k` by metis_tac[] >>
  `eval_operand (Var dv) t = SOME (n2w (B + 32)) /\
   eval_operand (Var ov) t = SOME ow` by
    (rewrite_tac[eval_operand_def] >> conj_tac >> first_assum ACCEPT_TAC) >>
  `(!z. Var dv = Var z ==> not_fresh_at s1 z) /\
   (!z. Var ov = Var z ==> not_fresh_at s1 z)` by
    (rw[] >> first_assum ACCEPT_TAC) >>
  `local_ptrs_rel func cenv es1.scopes t` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `compile_concat _ _ (_::_) _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [LET_THM]) >>
  Cases_on `is_bytestring_type (expr_type e)` >> asm_rewrite_tac[] >> strip_tac
  >- suspend "bytes"
  >> suspend "fixed"
QED

Resume concat_head_arm_mem[bytes]:
  drule compile_concat_bytes_cons >> strip_tac >>
  `mem_ptr = op /\ s1' = s1` by
    (qpat_x_assum `lower_value _ _ _ _ _ = (mem_ptr, _)` mp_tac >>
     asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `mem_ptr = op` SUBST_ALL_TAC >>
  qpat_x_assum `s1' = s1` SUBST_ALL_TAC >>
  drule concat_bytes_step_mono >> strip_tac >>
  `ci_mono s2 sb` by
    metis_tac[ci_mono_compile_concat_cfn, cj 1 compile_expr_ci_mono, pairTheory.SND] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    (fs[ci_mono_def] >>
     `cs_extends sa s2` by metis_tac[cs_extends_trans] >>
     `cs_extends sb sb` by rewrite_tac[cs_extends_refl] >>
     metis_tac[fn_has_code_mid]) >>
  drule_all concat_bytes_value >> strip_tac >>
  drule_all concat_bytestring_source_bound_mem >> strip_tac >>
  `32 + k + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) <= bsz` by decide_tac >>
  drule_all concat_bytes_arm_mem >> strip_tac >>
  suspend "assemble_bytes"
QED

Resume concat_head_arm_mem[fixed]:
  `?m. expr_type e = BaseT (BytesT (Fixed m))` by fs[] >>
  qpat_x_assum `compile_concat _ _ (_::_) _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> simp[] >> strip_tac >>
  drule compile_concat_fixed_cons >> strip_tac >>
  `v' = op /\ s1' = s1` by
    (qpat_x_assum `lower_value _ _ _ _ _ = (v', _)` mp_tac >>
     asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `v' = op` SUBST_ALL_TAC >>
  qpat_x_assum `s1' = s1` SUBST_ALL_TAC >>
  drule concat_fixed_step_mono >> strip_tac >>
  `ci_mono s2 sb` by
    metis_tac[ci_mono_compile_concat_cfn, cj 1 compile_expr_ci_mono, pairTheory.SND] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    (fs[ci_mono_def] >>
     `cs_extends sa s2` by metis_tac[cs_extends_trans] >>
     `cs_extends sb sb` by rewrite_tac[cs_extends_refl] >>
     metis_tac[fn_has_code_mid]) >>
  `expr_val_rel cx (BaseT (BytesT (Fixed m))) v op t` by metis_tac[] >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv` by metis_tac[] >>
  drule_all concat_fixed_value >> strip_tac >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  `32 + k + 32 <= bsz` by
    (qpat_x_assum `32 + concat_data_bound _ _ <= _` mp_tac >>
     asm_simp_tac (srw_ss()) [concat_data_bound_def, LET_THM,
                              is_bytestring_type_def] >>
     rewrite_tac[arithmeticTheory.MAX_DEF] >> IF_CASES_TAC >> decide_tac) >>
  `concat_payload_capacity (expr_type e) = m` by
    asm_simp_tac (srw_ss()) [concat_payload_capacity_def] >>
  drule_all concat_fixed_arm_mem >> strip_tac >>
  suspend "assemble_fixed"
QED

Resume concat_head_arm_mem[assemble_bytes]:
  drule_all concat_head_endpoint_frame_mem >> strip_tac >>
  qexistsl_tac [`s2`, `t2`] >>
  `k + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) <= P + concat_payload_capacity (expr_type e)` by decide_tac >>
  conj_tac >- (qpat_x_assum `compile_concat _ _ args _ _ _ _ = _` mp_tac >> simp[LET_THM]) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!name lb lsz. local_region _ _ t2 _ _ _ ==> _` drule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!p n. _ ==> mem_bytes_at p n t2.vs_memory = _` irule >> decide_tac
QED

Resume concat_head_arm_mem[assemble_fixed]:
  drule_all concat_head_endpoint_frame_mem >> strip_tac >>
  qexistsl_tac [`s2`, `t2`] >>
  conj_tac >- (qpat_x_assum `compile_concat _ _ args _ _ _ _ = _` mp_tac >> simp[LET_THM]) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!name lb lsz. local_region _ _ t2 _ _ _ ==> _` drule >> simp[]) >>
  conj_tac >- (simp[concat_payload_capacity_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!p n. _ ==> mem_bytes_at p n t2.vs_memory = _` irule >> decide_tac
QED

Finalise concat_head_arm_mem
