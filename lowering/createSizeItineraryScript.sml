(* Static CREATE action itineraries. The entries are compiler cuts, not PCs
   visited by an execution. The initial compiler state is not in cuts. *)
Theory createSizeItinerary
Ancestors
  createSizeCutCode createSizeCutEntry createSizeDispatch dallocaCreateGeometry
  stmtLoweringMono exprLoweringProps exprLowering builtinCreate compileEnv
  emitHelper loweringShapeRules venomInst list rich_list arithmetic pair context

Definition create_itinerary_code_def:
  (create_itinerary_code a [] b <=> a = b) /\
  (create_itinerary_code a (m::cuts) b <=>
    create_cut_code {} a m /\ create_cut_first a m /\ ci_mono a m /\
    create_itinerary_code m cuts b)
End

Theorem create_itinerary_code_append[simp]:
  !xs a ys b. create_itinerary_code a (xs ++ ys) b <=>
    ?m. create_itinerary_code a xs m /\ create_itinerary_code m ys b
Proof
  Induct >> simp[create_itinerary_code_def] >> metis_tac[]
QED

Theorem create_itinerary_code_relations:
  !cuts a b. create_itinerary_code a cuts b ==>
    LAST (a::cuts) = b /\
    LIST_REL (create_cut_code {}) (FRONT (a::cuts)) cuts /\
    LIST_REL create_cut_first (FRONT (a::cuts)) cuts /\ ci_mono a b
Proof
  Induct >> simp[create_itinerary_code_def, ci_mono_refl, FRONT_CONS] >>
  metis_tac[ci_mono_trans]
QED

(* Consecutive and nonconsecutive itinerary cuts can delimit a code band. *)
Theorem create_itinerary_index_mono:
  !cuts a b. create_itinerary_code a cuts b ==>
    !i j. i <= j /\ j <= LENGTH cuts ==>
      ci_mono (EL i (a::cuts)) (EL j (a::cuts))
Proof
  Induct >- simp[ci_mono_refl] >>
  simp[create_itinerary_code_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum (drule_then assume_tac) >>
  Cases_on `j` >- simp[ci_mono_refl] >>
  Cases_on `i` >> simp[EL] >> strip_tac
  >- (irule ci_mono_trans >> qexists_tac `h` >> simp[] >>
      first_x_assum (qspecl_then [`0`,`n`] mp_tac) >> simp[EL]) >>
  first_x_assum irule >> simp[]
QED

(* Suppliers characterize only compiler runs. They do not refer to a
   machine state or execution, so the closed form can instantiate them. *)
Definition create_itinerary_suppliers_def:
  create_itinerary_suppliers <=>
    (!ce ty e a. create_cut_code {} a (SND (compile_expr ce ty e a))) /\
    (!ce ty e a. create_cut_code {} a (SND (lower_value compile_expr ce ty e a))) /\
    (!ce copy vv a. create_cut_code {} a (SND (compile_snapshot_vv ce copy vv a))) /\
    (!ce vv a. create_cut_code {} a (SND (unwrap_value ce vv a))) /\
    (!ce vv ty a. create_cut_code {} a (SND (compile_create_snapshot ce vv ty a))) /\
    (!n a. create_cut_code {} a (SND (compile_alloc_buffer n a))) /\
    (!ce dst rows a. create_cut_code {} a
       (SND (compile_abi_encode_values_to_buf ce dst rows a))) /\
    (!target a. create_cut_code {} a (SND (compile_create_proxy_buf target a))) /\
    (!islit target off a. create_cut_code {} a
       (SND (compile_create_blueprint_check islit target off a)))
End

Theorem create_itinerary_action_facts[local]:
  create_itinerary_suppliers ==>
    (!ce ty e a v b. compile_expr ce ty e a = (v,b) ==>
      create_cut_code {} a b /\ create_cut_first a b /\ ci_mono a b) /\
    (!ce ty e a v b. lower_value compile_expr ce ty e a = (v,b) ==>
      create_cut_code {} a b /\ create_cut_first a b /\ ci_mono a b) /\
    (!ce copy vv a v b. compile_snapshot_vv ce copy vv a = (v,b) ==>
      create_cut_code {} a b /\ create_cut_first a b /\ ci_mono a b) /\
    (!ce vv a v b. unwrap_value ce vv a = (v,b) ==>
      create_cut_code {} a b /\ create_cut_first a b /\ ci_mono a b) /\
    (!ce vv ty a v b. compile_create_snapshot ce vv ty a = (v,b) ==>
      create_cut_code {} a b /\ create_cut_first a b /\ ci_mono a b) /\
    (!n a v b. compile_alloc_buffer n a = (v,b) ==>
      create_cut_code {} a b /\ create_cut_first a b /\ ci_mono a b) /\
    (!ce dst rows a v b. compile_abi_encode_values_to_buf ce dst rows a = (v,b) ==>
      create_cut_code {} a b /\ create_cut_first a b /\ ci_mono a b) /\
    (!target a v b. compile_create_proxy_buf target a = (v,b) ==>
      create_cut_code {} a b /\ create_cut_first a b /\ ci_mono a b) /\
    (!islit target off a v b. compile_create_blueprint_check islit target off a = (v,b) ==>
      create_cut_code {} a b /\ create_cut_first a b /\ ci_mono a b)
Proof
  rewrite_tac[create_itinerary_suppliers_def] >> strip_tac >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  TRY (drule_then strip_assume_tac (cj 1 create_cut_first_preparation)) >>
  TRY (drule_then strip_assume_tac (cj 2 create_cut_first_preparation)) >>
  TRY (drule_then strip_assume_tac (cj 3 create_cut_first_preparation)) >>
  TRY (FIRST (map (fn th => drule_then assume_tac th)
                 (List.drop (CONJUNCTS create_cut_first_actions,4)))) >>
  fs[] >>
  metis_tac[pairTheory.SND, ci_mono_compile_expr_sa,
    ci_mono_compile_snapshot_vv, ci_mono_unwrap_value,
    ci_mono_compile_create_snapshot, ci_mono_compile_alloc_buffer,
    ci_mono_compile_abi_encode_values_to_buf, ci_mono_compile_create_proxy_buf,
    ci_mono_compile_create_blueprint_check]
QED

Theorem create_itinerary_emit_facts[local]:
  (!opc ops a v b. emit_op opc ops a = (v,b) /\ opc <> PHI /\
      create_cut_targets opc ops = [] ==>
      create_cut_code {} a b /\ create_cut_first a b /\ ci_mono a b) /\
  (!opc ops a v b. emit_void opc ops a = (v,b) /\ opc <> PHI /\
      create_cut_targets opc ops = [] ==>
      create_cut_code {} a b /\ create_cut_first a b /\ ci_mono a b) /\
  (!opc ops outs a v b. emit_inst opc ops outs a = (v,b) /\ opc <> PHI /\
      create_cut_targets opc ops = [] ==>
      create_cut_code {} a b /\ create_cut_first a b /\ ci_mono a b)
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (drule_all (cj 2 create_cut_first_actions) >> strip_tac >>
      metis_tac[create_cut_code_emit_op, ci_mono_emit_op, MEM, pairTheory.SND])
  >- (drule_all (cj 3 create_cut_first_actions) >> strip_tac >>
      metis_tac[create_cut_code_emit_void, ci_mono_emit_void, MEM, pairTheory.SND])
  >> drule_all (cj 4 create_cut_first_actions) >> strip_tac >>
     metis_tac[create_cut_code_emit_inst, ci_mono_emit_inst, MEM, pairTheory.SND]
QED

Theorem create_itinerary_mem_facts[local]:
  (!n a v b. compile_alloc_dynamic n a = (v,b) ==>
    create_cut_code {} a b /\ create_cut_first a b /\ ci_mono a b) /\
  (!dst src n a v b. compile_copy_memory_dynamic dst src n a = (v,b) ==>
    create_cut_code {} a b /\ create_cut_first a b /\ ci_mono a b)
Proof
  simp[compile_alloc_dynamic_def, compile_copy_memory_dynamic_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  FIRST [irule (cj 1 create_itinerary_emit_facts) >>
           qexistsl_tac [`DALLOCA`,`[n]`,`v`] >> simp[create_cut_targets_def] >> NO_TAC,
         irule (cj 2 create_itinerary_emit_facts) >>
           qexistsl_tac [`MCOPY`,`[dst;src;n]`,`v`] >> simp[create_cut_targets_def]]
QED

(* A theorem of one adjacent edge can be used by combining its three
   projections in the goals left by unfolding create_itinerary_code. *)
fun itinerary_edges ths =
  fs (create_itinerary_code_def :: create_cut_targets_def :: ci_mono_refl ::
      CONJUNCTS create_itinerary_emit_facts @ CONJUNCTS create_itinerary_mem_facts @ ths);

Definition create_itinerary_ctor_rows_def:
  create_itinerary_ctor_rows ce es vals a b cs mid vs <=>
    LENGTH cs = SUC (LENGTH es) /\ HD cs = a /\ LAST cs = b /\
    LENGTH mid = LENGTH es /\ LENGTH vs = LENGTH es /\ LENGTH vals = LENGTH es /\
    !i. i < LENGTH es ==>
      compile_expr ce (expr_type (EL i es)) (EL i es) (EL i cs) =
        (EL i vs, EL i mid) /\
      compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) es))
        (ext_call_arg_value (lowered_value_type ce (EL i es)) (EL i vs)) (EL i mid) =
        (EL i vals, EL (SUC i) cs)
End

Definition create_itinerary_rows_supplier_def:
  create_itinerary_rows_supplier <=>
    !ce es a vals b. compile_create_ctor_args compile_expr ce es a = (vals,b) ==>
      ?cs mid vs. create_itinerary_ctor_rows ce es vals a b cs mid vs
End

Definition create_itinerary_ctor_cuts_def:
  create_itinerary_ctor_cuts cs mid n =
    FLAT (GENLIST (\i. [EL i mid; EL (SUC i) cs]) n)
End

Theorem create_itinerary_pairs[local]:
  !n c m.
    (!i. i < n ==> create_itinerary_code (c i) [m i;c (SUC i)] (c (SUC i))) ==>
    create_itinerary_code (c 0) (FLAT (GENLIST (\i. [m i;c (SUC i)]) n)) (c n)
Proof
  Induct >- simp[create_itinerary_code_def] >>
  rpt gen_tac >> strip_tac >> simp[GENLIST_CONS] >>
  `create_itinerary_code (c 0) [m 0;c (SUC 0)] (c (SUC 0))` by simp[] >>
  `create_itinerary_code (c (SUC 0))
     (FLAT (GENLIST ((\i. [m i;c (SUC i)]) o SUC) n)) (c (SUC n))` by
    (first_x_assum (qspecl_then [`c o SUC`,`m o SUC`] mp_tac) >>
     simp[combinTheory.o_DEF] >> metis_tac[LESS_MONO_EQ]) >>
  fs[create_itinerary_code_def]
QED

Theorem create_itinerary_ctor_rows_code[local]:
  create_itinerary_suppliers /\ create_itinerary_ctor_rows ce es vals a b cs mid vs ==>
  create_itinerary_code a (create_itinerary_ctor_cuts cs mid (LENGTH es)) b
Proof
  strip_tac >> drule create_itinerary_action_facts >> strip_tac >>
  fs[create_itinerary_ctor_rows_def, create_itinerary_ctor_cuts_def] >>
  `cs <> []` by (strip_tac >> fs[]) >>
  `a = EL 0 cs /\ b = EL (LENGTH es) cs` by
    (Cases_on `cs` >> gvs[LAST_EL]) >>
  qpat_x_assum `a = EL 0 cs` SUBST_ALL_TAC >>
  qpat_x_assum `b = EL _ cs` SUBST_ALL_TAC >>
  qspecl_then [`LENGTH es`,`\i. EL i cs`,`\i. EL i mid`] mp_tac
    create_itinerary_pairs >> BETA_TAC >> disch_then irule >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!i. _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  qpat_assum `!ce ty e a v b. compile_expr ce ty e a = (v,b) ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!ce copy vv a v b. compile_snapshot_vv ce copy vv a = (v,b) ==> _`
    (drule_then strip_assume_tac) >>
  simp[create_itinerary_code_def]
QED

Definition create_itinerary_salt_def:
  (create_itinerary_salt ce NONE a salt b <=> salt = NONE /\ b = a) /\
  (create_itinerary_salt ce (SOME e) a salt b <=> ?x.
    salt = SOME x /\ lower_value compile_expr ce (expr_type e) e a = (x,b))
End

Theorem create_itinerary_salt_run[local]:
  create_itinerary_suppliers /\ compile_create_salt compile_expr ce e a = (salt,b) ==>
  create_itinerary_salt ce e a salt b /\ create_itinerary_code a [b] b
Proof
  Cases_on `e` >>
  simp[compile_create_salt_def, comp_return_def, comp_bind_def, create_itinerary_salt_def] >>
  TRY pairarg_tac >> simp[] >> strip_tac >>
  gvs[create_itinerary_code_def, ci_mono_refl] >>
  drule create_itinerary_action_facts >> strip_tac >>
  qpat_assum `!ce ty e a v b. lower_value _ _ _ _ _ = (v,b) ==> _`
    (drule_then strip_assume_tac) >> simp[]
QED

Theorem create_itinerary_dispatch_run[local]:
  compile_create_dispatch bufop len value salt rof sc = (result,sb) ==>
  ?sd created. create_size_dispatch_tail rof sc sd created bufop len value salt result sb
Proof
  Cases_on `salt` >> simp[compile_create_dispatch_def, create_size_dispatch_tail_def,
                          comp_bind_def] >> pairarg_tac >> simp[] >> metis_tac[]
QED

Definition create_proxy_itinerary_def[local]:
  create_proxy_itinerary ce salted args sa cuts value salt buf len <=>
    ?target_e value_e rest target a b c sc.
      args = target_e::value_e::rest /\ (salted ==> rest <> []) /\
      lower_value compile_expr ce (expr_type target_e) target_e sa = (target,a) /\
      lower_value compile_expr ce (expr_type value_e) value_e a = (value,b) /\
      compile_create_proxy_buf target b = (buf,c) /\
      create_itinerary_salt ce (if salted then SOME (HD rest) else NONE) c salt sc /\
      cuts = [a;b;c;sc] /\ len = Lit 54w
End

Theorem create_proxy_itinerary_eq:
  create_proxy_itinerary ce salted args sa cuts value salt buf len <=>
    ?target_e value_e rest target a b c sc.
      args = target_e::value_e::rest /\ (salted ==> rest <> []) /\
      lower_value compile_expr ce (expr_type target_e) target_e sa = (target,a) /\
      lower_value compile_expr ce (expr_type value_e) value_e a = (value,b) /\
      compile_create_proxy_buf target b = (buf,c) /\
      create_itinerary_salt ce (if salted then SOME (HD rest) else NONE) c salt sc /\
      cuts = [a;b;c;sc] /\ len = Lit 54w
Proof
  simp[create_proxy_itinerary_def]
QED

Definition create_copy_itinerary_def:
  create_copy_itinerary ce salted args sa cuts value salt buf len <=>
    ?target_e value_e rest target a b c code a1 a2 shifted a3 preamble a4 size a5
       alloc_ptr a6 a7 code_dst a8 a9 a10 sc.
      args = target_e::value_e::rest /\ (salted ==> rest <> []) /\
      lower_value compile_expr ce (expr_type target_e) target_e sa = (target,a) /\
      lower_value compile_expr ce (expr_type value_e) value_e a = (value,b) /\
      create_itinerary_salt ce (if salted then SOME (HD rest) else NONE) b salt c /\
      emit_op EXTCODESIZE [target] c = (code,a1) /\
      emit_void ASSERT [code] a1 = ((),a2) /\
      emit_op SHL [Lit 56w;code] a2 = (shifted,a3) /\
      emit_op OR [Lit 0x620000003d81600b3d39f3w;shifted] a3 = (preamble,a4) /\
      emit_op ADD [code;Lit 32w] a4 = (size,a5) /\
      compile_alloc_dynamic size a5 = (alloc_ptr,a6) /\
      emit_void MSTORE [alloc_ptr;preamble] a6 = ((),a7) /\
      emit_op ADD [alloc_ptr;Lit 32w] a7 = (code_dst,a8) /\
      emit_void EXTCODECOPY [target;code_dst;Lit 0w;code] a8 = ((),a9) /\
      emit_op ADD [alloc_ptr;Lit 21w] a9 = (buf,a10) /\
      emit_op ADD [code;Lit 11w] a10 = (len,sc) /\
      cuts = [a;b;c;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;sc]
End

Theorem create_proxy_itinerary_run[local]:
  create_itinerary_suppliers /\ (salted ==> rest <> []) /\
  compile_create_call compile_expr ce CreateMinimalProxy salted rof
    (target_e::value_e::rest) sa = (result,sb) ==>
  ?cuts value salt buf sc sd created.
    create_proxy_itinerary ce salted (target_e::value_e::rest) sa cuts value salt buf (Lit 54w) /\
    create_itinerary_code sa cuts sc /\
    create_size_dispatch_tail rof sc sd created buf (Lit 54w) value salt result sb
Proof
  simp_tac (srw_ss()) [compile_create_call_def, LET_THM] >>
  strip_tac >>
  `~(LENGTH rest < (if salted then 1 else 0))` by (Cases_on `salted` >> Cases_on `rest` >> fs[]) >>
  fs[comp_bind_def] >> rpt (pairarg_tac >> fs[]) >>
  drule_all create_itinerary_salt_run >> strip_tac >>
  drule create_itinerary_dispatch_run >> strip_tac >>
  rename1 `lower_value compile_expr ce (expr_type target_e) target_e sa = (target,a)` >>
  rename1 `lower_value compile_expr ce (expr_type value_e) value_e a = (value,b)` >>
  rename1 `compile_create_proxy_buf target b = (buf,c)` >>
  rename1 `create_itinerary_salt ce _ c salt sc` >>
  qexists_tac `[a;b;c;sc]` >>
  simp[create_proxy_itinerary_def] >>
  rpt (goal_assum (drule_at Any)) >>
  imp_res_tac create_itinerary_action_facts >>
  itinerary_edges []
QED

fun itinerary_certify () =
  imp_res_tac create_itinerary_action_facts >>
  imp_res_tac create_itinerary_mem_facts >>
  imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO] create_itinerary_emit_facts) >>
  fs[create_cut_targets_def] >> itinerary_edges [];

Theorem create_copy_itinerary_run[local]:
  create_itinerary_suppliers /\ (salted ==> rest <> []) /\
  compile_create_call compile_expr ce CreateCopyOf salted rof
    (target_e::value_e::rest) sa = (result,sb) ==>
  ?cuts value salt buf len sc sd created.
    create_copy_itinerary ce salted (target_e::value_e::rest) sa cuts value salt buf len /\
    create_itinerary_code sa cuts sc /\
    create_size_dispatch_tail rof sc sd created buf len value salt result sb
Proof
  simp_tac (srw_ss()) [compile_create_call_def, LET_THM] >> strip_tac >>
  `~(LENGTH rest < (if salted then 1 else 0))` by (Cases_on `salted` >> Cases_on `rest` >> fs[]) >>
  fs[comp_bind_def] >> rpt (pairarg_tac >> fs[]) >>
  drule_all create_itinerary_salt_run >> strip_tac >>
  drule create_copy_create_prefix >> strip_tac >>
  rename1 `lower_value compile_expr ce (expr_type target_e) target_e sa = (target,a)` >>
  rename1 `lower_value compile_expr ce (expr_type value_e) value_e a = (value,b)` >>
  rename1 `create_itinerary_salt ce _ b salt c` >>
  qexists_tac `[a;b;c;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;sc]` >>
  simp[create_copy_itinerary_def, create_size_dispatch_tail_def] >>
  rpt (goal_assum (drule_at Any)) >> itinerary_certify ()
QED

Definition create_raw_prep_itinerary_def:
  create_raw_prep_itinerary ce es size data len a cuts bufop total b <=>
    (es = [] /\ cuts = [] /\ bufop = data /\ total = len /\ b = a) \/
    (es <> [] /\ ?vals k cs mid vs buf p q dst r args_len u.
      compile_create_ctor_args compile_expr ce es a = (vals,k) /\
      create_itinerary_ctor_rows ce es vals a k cs mid vs /\
      compile_alloc_buffer size k = (buf,p) /\
      compile_copy_memory_dynamic buf.buf_operand data len p = ((),q) /\
      emit_op ADD [buf.buf_operand;len] q = (dst,r) /\
      compile_abi_encode_values_to_buf ce dst
        (ZIP (vals,MAP (lowered_value_type ce) es)) r = (args_len,u) /\
      emit_op ADD [len;args_len] u = (total,b) /\ bufop = buf.buf_operand /\
      cuts = create_itinerary_ctor_cuts cs mid (LENGTH es) ++ [p;q;r;u;b])
End

Theorem create_raw_prep_itinerary_run[local]:
  !size total. create_itinerary_suppliers /\ create_itinerary_rows_supplier /\
  (if es = [] then comp_return (data,len) else
   comp_bind (compile_create_ctor_args compile_expr ce es) (\vals.
   comp_bind (compile_alloc_buffer size) (\buf.
   comp_ignore_bind (compile_copy_memory_dynamic buf.buf_operand data len)
     (comp_bind (emit_op ADD [buf.buf_operand;len]) (\dst.
      comp_bind (compile_abi_encode_values_to_buf ce dst
                   (ZIP (vals,MAP (lowered_value_type ce) es))) (\args_len.
      comp_bind (emit_op ADD [len;args_len]) (\total.
      comp_return (buf.buf_operand,total)))))))) a = ((bufop,total),b) ==>
  ?cuts. create_raw_prep_itinerary ce es size data len a cuts bufop total b /\
         create_itinerary_code a cuts b
Proof
  Cases_on `es = []`
  >- simp[comp_return_def, create_raw_prep_itinerary_def, create_itinerary_code_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  qpat_assum `create_itinerary_rows_supplier`
    (drule_then strip_assume_tac o REWRITE_RULE [create_itinerary_rows_supplier_def]) >>
  drule_all create_itinerary_ctor_rows_code >> strip_tac >>
  rename1 `compile_alloc_buffer n k = (buf,p)` >>
  rename1 `compile_copy_memory_dynamic buf.buf_operand data len p = ((),q)` >>
  rename1 `emit_op ADD [buf.buf_operand;len] q = (dst,r)` >>
  rename1 `compile_abi_encode_values_to_buf ce dst _ r = (args_len,u)` >>
  qexists_tac `create_itinerary_ctor_cuts cs mid (LENGTH es) ++ [p;q;r;u;b]` >>
  simp[create_raw_prep_itinerary_def] >>
  rpt (goal_assum (drule_at Any)) >>
  conj_tac >- (qexistsl_tac [`cs`,`mid`,`vs`] >> simp[]) >>
  qexists_tac `k` >> simp[] >> itinerary_certify ()
QED

Definition create_raw_itinerary_def:
  create_raw_itinerary ce salted args sa cuts value salt bufop total <=>
    ?bytecode_e value_e rest vv a bytes b len c data d prep p q sc.
      args = bytecode_e::value_e::rest /\ (salted ==> rest <> []) /\
      compile_expr ce (expr_type bytecode_e) bytecode_e sa = (vv,a) /\
      compile_create_snapshot ce vv (lowered_value_type ce bytecode_e) a = (bytes,b) /\
      emit_op MLOAD [bytes] b = (len,c) /\ emit_op ADD [bytes;Lit 32w] c = (data,d) /\
      create_raw_prep_itinerary ce (if salted then FRONT rest else rest)
        (bytelike_type_bound (lowered_value_type ce bytecode_e) +
         abi_size_bound ce.ce_struct_fields
           (TupleT (MAP (lowered_value_type ce) (if salted then FRONT rest else rest))))
        data len d prep bufop total p /\
      lower_value compile_expr ce (expr_type value_e) value_e p = (value,q) /\
      create_itinerary_salt ce (if salted then SOME (LAST rest) else NONE) q salt sc /\
      cuts = [a;b;c;d] ++ prep ++ [q;sc]
End

Theorem create_raw_itinerary_run[local]:
  create_itinerary_suppliers /\ create_itinerary_rows_supplier /\ (salted ==> rest <> []) /\
  compile_create_call compile_expr ce RawCreate salted rof
    (bytecode_e::value_e::rest) sa = (result,sb) ==>
  ?cuts value salt bufop total sc sd created.
    create_raw_itinerary ce salted (bytecode_e::value_e::rest) sa cuts value salt bufop total /\
    create_itinerary_code sa cuts sc /\
    create_size_dispatch_tail rof sc sd created bufop total value salt result sb
Proof
  simp_tac (srw_ss()) [compile_create_call_def, compile_raw_create_def, LET_THM] >> strip_tac >>
  `~(LENGTH rest < (if salted then 1 else 0))` by (Cases_on `salted` >> Cases_on `rest` >> fs[]) >>
  fs[comp_bind_def] >> ntac 4 (pairarg_tac >> fs[]) >>
  pairarg_tac >> rename1 `_ = (payload,p)` >> PairCases_on `payload` >>
  fs[comp_bind_def] >> rpt (pairarg_tac >> fs[]) >>
  drule_all create_raw_prep_itinerary_run >> strip_tac >>
  drule_all create_itinerary_salt_run >> strip_tac >>
  drule create_itinerary_dispatch_run >> strip_tac >>
  rename1 `compile_expr ce (expr_type bytecode_e) bytecode_e sa = (vv,a)` >>
  rename1 `compile_create_snapshot ce vv _ a = (bytes,b)` >>
  rename1 `emit_op MLOAD [bytes] b = (len,c)` >>
  rename1 `emit_op ADD [bytes;Lit 32w] c = (data,d)` >>
  rename1 `create_raw_prep_itinerary ce _ _ data len d prep bufop total_op p` >>
  rename1 `lower_value compile_expr ce (expr_type value_e) value_e p = (value,q)` >>
  rename1 `create_itinerary_salt ce _ q salt sc` >>
  qexists_tac `[a;b;c;d] ++ prep ++ [q;sc]` >>
  simp[create_raw_itinerary_def] >>
  rpt (goal_assum (drule_at Any)) >>
  itinerary_certify () >> conj_tac >> qexists_tac `p` >> simp[]
QED

Definition create_blueprint_args_itinerary_def:
  create_blueprint_args_itinerary ce raw later es a cuts bufop len b <=>
    (raw /\ ?e vv p snap q loc r m.
      es = [e] /\ compile_expr ce (expr_type e) e a = (vv,p) /\
      compile_snapshot_vv ce (exprs_can_mutate ce later) vv p = (snap,q) /\
      unwrap_value ce snap q = (loc,r) /\ emit_op MLOAD [loc] r = (len,m) /\
      emit_op ADD [loc;Lit 32w] m = (bufop,b) /\ cuts = [p;q;r;m;b]) \/
    (raw /\ (!e. es <> [e]) /\ emit_inst INVALID [] [] a = ((),b) /\
      bufop = Lit 0w /\ len = Lit 0w /\ cuts = [b]) \/
    (~raw /\ es = [] /\ bufop = Lit 0w /\ len = Lit 0w /\ cuts = [] /\ b = a) \/
    (~raw /\ es <> [] /\ ?vals k cs mid vs buf m.
      compile_create_ctor_args compile_expr ce es a = (vals,k) /\
      create_itinerary_ctor_rows ce es vals a k cs mid vs /\
      compile_alloc_buffer (abi_size_bound ce.ce_struct_fields
        (TupleT (MAP (lowered_value_type ce) es))) k = (buf,m) /\
      compile_abi_encode_values_to_buf ce buf.buf_operand
        (ZIP (vals,MAP (lowered_value_type ce) es)) m = (len,b) /\
      bufop = buf.buf_operand /\ cuts = create_itinerary_ctor_cuts cs mid (LENGTH es) ++ [m;b])
End

Theorem create_blueprint_args_itinerary_raw[local]:
  create_itinerary_suppliers /\
  compile_create_blueprint_args compile_expr ce T later es a = ((bufop,len),b) ==>
  ?cuts. create_blueprint_args_itinerary ce T later es a cuts bufop len b /\
         create_itinerary_code a cuts b
Proof
  Cases_on `es` >> TRY (rename1 `h::t` >> Cases_on `t`) >>
  simp[compile_create_blueprint_args_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> fs[]) >> gvs[] >>
  TRY (qexists_tac `[b]` >> simp[create_blueprint_args_itinerary_def] >>
       rpt (goal_assum (drule_at Any)) >> itinerary_certify () >> NO_TAC) >>
  rename1 `compile_expr ce (expr_type e) e a = (vv,p)` >>
  rename1 `compile_snapshot_vv ce _ vv p = (snap,q)` >>
  rename1 `unwrap_value ce snap q = (loc,r)` >>
  rename1 `emit_op MLOAD [loc] r = (len,m)` >>
  qexists_tac `[p;q;r;m;b]` >> simp[create_blueprint_args_itinerary_def] >>
  rpt (goal_assum (drule_at Any)) >> itinerary_certify ()
QED

Theorem create_blueprint_args_itinerary_run[local]:
  create_itinerary_suppliers /\ create_itinerary_rows_supplier /\
  compile_create_blueprint_args compile_expr ce raw later es a = ((bufop,len),b) ==>
  ?cuts. create_blueprint_args_itinerary ce raw later es a cuts bufop len b /\
         create_itinerary_code a cuts b
Proof
  Cases_on `raw` >- metis_tac[create_blueprint_args_itinerary_raw] >>
  Cases_on `es = []`
  >- simp[compile_create_blueprint_args_def, comp_return_def,
          create_blueprint_args_itinerary_def, create_itinerary_code_def] >>
  simp[compile_create_blueprint_args_def, comp_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> fs[]) >> gvs[] >>
  qpat_assum `create_itinerary_rows_supplier`
    (drule_then strip_assume_tac o REWRITE_RULE [create_itinerary_rows_supplier_def]) >>
  drule_all create_itinerary_ctor_rows_code >> strip_tac >>
  rename1 `compile_alloc_buffer _ k = (buf,m)` >>
  qexists_tac `create_itinerary_ctor_cuts cs mid (LENGTH es) ++ [m;b]` >>
  simp[create_blueprint_args_itinerary_def] >> rpt (goal_assum (drule_at Any)) >>
  conj_tac >- (qexistsl_tac [`cs`,`mid`,`vs`] >> simp[]) >>
  qexists_tac `k` >> simp[] >> itinerary_certify ()
QED

Definition create_blueprint_offset_run_def:
  create_blueprint_offset_run ce e a off b <=>
    (case origin_fold_value e of
       Literal _ (IntL i) => comp_return (Lit (i2w i))
     | _ => lower_value compile_expr ce (expr_type e) e) a = (off,b)
End

Theorem create_blueprint_offset_code[local]:
  create_itinerary_suppliers /\ create_blueprint_offset_run ce e a off b ==>
  create_itinerary_code a [b] b
Proof
  Cases_on `origin_fold_value e` >> simp[create_blueprint_offset_run_def] >>
  TRY (rename1 `origin_fold_value e = Literal ann lit` >> Cases_on `lit` >> simp[]) >>
  strip_tac >> gvs[comp_return_def,create_itinerary_code_def,ci_mono_refl] >>
  drule_then (drule_then strip_assume_tac o cj 2) create_itinerary_action_facts >> simp[]
QED

Definition create_blueprint_append_itinerary_def:
  create_blueprint_append_itinerary target off code args_buf args_len a cuts bufop len <=>
    ?m n p.
      emit_op ADD [code;args_len] a = (len,m) /\
      compile_alloc_dynamic len m = (bufop,n) /\
      emit_void EXTCODECOPY [target;bufop;off;code] n = ((),p) /\
      (if args_len = Lit 0w then cuts = [m;n;p] else
        ?dest q sc. emit_op ADD [bufop;code] p = (dest,q) /\
         compile_copy_memory_dynamic dest args_buf args_len q = ((),sc) /\
         cuts = [m;n;p;q;sc])
End

Theorem create_blueprint_append_itinerary_run[local]:
  compile_create_blueprint_append target value salt off code args_buf args_len rof a =
    (result,sb) ==>
  ?cuts bufop len sc sd created.
    create_blueprint_append_itinerary target off code args_buf args_len a cuts bufop len /\
    create_itinerary_code a cuts sc /\
    create_size_dispatch_tail rof sc sd created bufop len value salt result sb
Proof
  strip_tac >> drule create_blueprint_create_prefix >> strip_tac >>
  Cases_on `args_len = Lit 0w` >> gvs[]
  >- (rename1 `emit_op ADD [code;Lit 0w] a = (len,m)` >>
      rename1 `compile_alloc_dynamic len m = (bufop,n)` >>
      rename1 `emit_void EXTCODECOPY [target;bufop;off;code] n = ((),p)` >>
      qexists_tac `[m;n;p]` >>
      simp[create_blueprint_append_itinerary_def, create_size_dispatch_tail_def] >>
      rpt (goal_assum (drule_at Any)) >> itinerary_certify ()) >>
  rename1 `emit_op ADD [code;args_len] a = (len,m)` >>
  rename1 `compile_alloc_dynamic len m = (bufop,n)` >>
  rename1 `emit_void EXTCODECOPY [target;bufop;off;code] n = ((),p)` >>
  rename1 `emit_op ADD [bufop;code] p = (dest,q)` >>
  qexists_tac `[m;n;p;q;sc]` >>
  simp[create_blueprint_append_itinerary_def, create_size_dispatch_tail_def] >>
  rpt (goal_assum (drule_at Any)) >> itinerary_certify ()
QED

Definition create_blueprint_itinerary_def:
  create_blueprint_itinerary ce raw salted args sa cuts value salt bufop len <=>
    ?target_e value_e rest suffix later target a prep args_buf args_len b c d off e code f app.
      args = target_e::value_e::rest /\ (if salted then 2 else 1) <= LENGTH rest /\
      suffix = (if salted then TL rest else rest) /\
      later = value_e :: TAKE (if salted then 2 else 1) rest /\
      lower_value compile_expr ce (expr_type target_e) target_e sa = (target,a) /\
      create_blueprint_args_itinerary ce raw later (TL suffix) a prep args_buf args_len b /\
      lower_value compile_expr ce (expr_type value_e) value_e b = (value,c) /\
      create_itinerary_salt ce (if salted then SOME (HD rest) else NONE) c salt d /\
      create_blueprint_offset_run ce (HD suffix) d off e /\
      compile_create_blueprint_check (is_int_literal (origin_fold_value (HD suffix)))
        target off e = (code,f) /\
      create_blueprint_append_itinerary target off code args_buf args_len f app bufop len /\
      cuts = a :: (prep ++ [c;d;e;f] ++ app)
End

Theorem create_blueprint_itinerary_run[local]:
  create_itinerary_suppliers /\ create_itinerary_rows_supplier /\
  (if salted then 2 else 1) <= LENGTH rest /\
  compile_create_call compile_expr ce (CreateFromBlueprint raw) salted rof
    (target_e::value_e::rest) sa = (result,sb) ==>
  ?cuts value salt bufop len sc sd created.
    create_blueprint_itinerary ce raw salted (target_e::value_e::rest) sa cuts value salt bufop len /\
    create_itinerary_code sa cuts sc /\
    create_size_dispatch_tail rof sc sd created bufop len value salt result sb
Proof
  simp_tac (srw_ss()) [compile_create_call_def, LET_THM] >> strip_tac >>
  `~(LENGTH rest < (if salted then 1 else 0) + 1)` by
    (Cases_on `salted` >> Cases_on `rest` >> fs[]) >>
  fs[comp_bind_def] >> pairarg_tac >> fs[] >>
  pairarg_tac >> rename1 `compile_create_blueprint_args _ _ _ _ _ _ = (payload,b)` >>
  PairCases_on `payload` >> fs[comp_bind_def] >> rpt (pairarg_tac >> fs[]) >>
  drule_all create_blueprint_args_itinerary_run >> strip_tac >>
  drule_all create_itinerary_salt_run >> strip_tac >>
  drule create_blueprint_append_itinerary_run >> strip_tac >>
  rename1 `lower_value compile_expr ce (expr_type target_e) target_e sa = (target,a)` >>
  rename1 `create_blueprint_args_itinerary ce raw _ _ a prep args_buf args_len b` >>
  rename1 `lower_value compile_expr ce (expr_type value_e) value_e b = (value,c)` >>
  rename1 `create_itinerary_salt ce _ c salt d` >>
  rename1 `compile_create_blueprint_check _ target off e = (code,f)` >>
  rename1 `create_blueprint_append_itinerary target off code args_buf args_len f app bufop len` >>
  `create_blueprint_offset_run ce (HD (if salted then TL rest else rest)) d off e` by
    fs[create_blueprint_offset_run_def] >>
  drule_all create_blueprint_offset_code >> strip_tac >>
  qexists_tac `a :: (prep ++ [c;d;e;f] ++ app)` >>
  simp[create_blueprint_itinerary_def] >> rpt (goal_assum (drule_at Any)) >>
  itinerary_certify () >> conj_tac
  >- (qexistsl_tac [`prep`,`args_buf`,`args_len`,`b`,`c`,`d`,`off`,`e`,`code`,`f`,`app`] >> simp[]) >>
  qexists_tac `f` >> simp[] >> qexists_tac `b` >> simp[]
QED

Definition create_call_itinerary_def:
  create_call_itinerary ce ck salted args sa cuts value salt bufop len <=>
    case ck of
      CreateMinimalProxy => create_proxy_itinerary ce salted args sa cuts value salt bufop len
    | CreateCopyOf => create_copy_itinerary ce salted args sa cuts value salt bufop len
    | RawCreate => create_raw_itinerary ce salted args sa cuts value salt bufop len
    | CreateFromBlueprint raw =>
        create_blueprint_itinerary ce raw salted args sa cuts value salt bufop len
End

Theorem create_call_itinerary_run:
  create_itinerary_suppliers /\ create_itinerary_rows_supplier /\
  compile_create_call compile_expr ce ck salted rof args sa = (result,sb) ==>
  (emit_inst INVALID [] [] sa = ((),sb) /\ result = Lit 0w) \/
  ?cuts value salt bufop len sc sd created.
    create_call_itinerary ce ck salted args sa cuts value salt bufop len /\
    create_itinerary_code sa cuts sc /\
    create_size_dispatch_tail rof sc sd created bufop len value salt result sb
Proof
  strip_tac >>
  `(?target_e value_e rest. args = target_e::value_e::rest /\
      ~ (LENGTH rest < (if salted then 1 else 0) +
          (case ck of CreateFromBlueprint _ => 1 | _ => 0))) \/
   (emit_inst INVALID [] [] sa = ((),sb) /\ result = Lit 0w)` by
    (Cases_on `args` >> TRY (rename1 `h::t` >> Cases_on `t`) >>
     TRY (disj1_tac >> goal_assum (drule_at Any) >> NO_TAC) >>
     TRY (rename1 `compile_create_call _ _ _ _ _ (_::_::rest) _ = _` >>
          Cases_on `LENGTH rest < (if salted then 1 else 0) +
            (case ck of CreateFromBlueprint _ => 1 | _ => 0)`) >>
     fs[compile_create_call_def, comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     rpt (pairarg_tac >> gvs[])) >>
  gvs[] >> Cases_on `ck` >> fs[create_call_itinerary_def] >>
  `salted ==> rest <> []` by (Cases_on `salted` >> Cases_on `rest` >> fs[]) >>
  FIRST [drule_all create_proxy_itinerary_run, drule_all create_copy_itinerary_run,
         drule_all create_raw_itinerary_run,
         `(if salted then 2 else 1) <= LENGTH rest` by
           (Cases_on `salted` >> Cases_on `rest` >> fs[]) >>
           drule_all create_blueprint_itinerary_run] >> metis_tac[]
QED
