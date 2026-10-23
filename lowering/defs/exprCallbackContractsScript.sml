(* Closed support contracts for every open-recursive helper reached by the
   expression compiler bodies. Equality is restricted to actual AST children,
   not all possible compiler callback inputs. *)
Theory exprCallbackContracts
Ancestors
  exprLowering exprCallBounds compileEnv context vyperAST list

Definition expr_callbacks_agree_def:
  expr_callbacks_agree f g cenv es =
    (∀ty e st. MEM e es ⇒ f cenv ty e st = g cenv ty e st)
End

Theorem expr_callbacks_agree_nil[simp]:
  expr_callbacks_agree f g cenv []
Proof
  simp[expr_callbacks_agree_def]
QED

Theorem expr_callbacks_agree_cons[simp]:
  expr_callbacks_agree f g cenv (e::es) ⇔
  (∀ty. f cenv ty e = g cenv ty e) ∧ expr_callbacks_agree f g cenv es
Proof
  simp[expr_callbacks_agree_def, FUN_EQ_THM, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem expr_callbacks_agree_append[simp]:
  expr_callbacks_agree f g cenv (xs ++ ys) ⇔
  expr_callbacks_agree f g cenv xs ∧ expr_callbacks_agree f g cenv ys
Proof
  simp[expr_callbacks_agree_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem expr_callbacks_agree_apply:
  expr_callbacks_agree f g cenv es ∧ MEM e es ⇒
  f cenv ty e = g cenv ty e
Proof
  simp[expr_callbacks_agree_def, FUN_EQ_THM]
QED

Theorem expr_child_callback_agrees:
  (∀e. MEM e es ⇒ expr_size e < bound) ⇒
  expr_callbacks_agree (expr_child_callback bound f) f cenv es
Proof
  simp[expr_callbacks_agree_def, expr_child_callback_def]
QED

Theorem compile_multi_vvs_callback_contract:
  ∀es. expr_callbacks_agree f g cenv es ⇒
    compile_multi_vvs f cenv es = compile_multi_vvs g cenv es
Proof
  Induct >> simp[compile_multi_vvs_def] >> rpt strip_tac >>
  gvs[expr_callbacks_agree_def, FUN_EQ_THM, comp_bind_def] >>
  simp[]
QED

Theorem compile_make_tuple_callback_contract:
  ∀es buf off. expr_callbacks_agree f g cenv es ⇒
    compile_make_tuple f cenv es buf off = compile_make_tuple g cenv es buf off
Proof
  Induct >> simp[compile_make_tuple_def] >> rpt strip_tac >>
  fs[] >> simp[lower_value_def]
QED

Theorem compile_make_array_callback_contract:
  ∀es sz lw (total:num) buf idx. expr_callbacks_agree f g cenv es ⇒
    compile_make_array f cenv es sz lw total buf idx =
    compile_make_array g cenv es sz lw total buf idx
Proof
  Induct >> simp[compile_make_array_def] >> rpt strip_tac >>
  fs[] >> simp[lower_value_def]
QED

Theorem compile_concat_callback_contract:
  ∀es dp infos off. expr_callbacks_agree f g cenv es ⇒
    compile_concat f cenv es dp infos off = compile_concat g cenv es dp infos off
Proof
  Induct >- simp[compile_concat_def] >>
  rpt gen_tac >> Cases_on `infos` >- simp[compile_concat_def] >>
  rename1 `compile_concat f cenv _ _ (info::rest_infos) _` >>
  Cases_on `info` >>
  simp[compile_concat_def] >> rpt strip_tac >>
  fs[] >> simp[lower_value_def]
QED

Theorem compile_struct_lit_callback_contract:
  ∀fields ty buf off. expr_callbacks_agree f g cenv (MAP SND fields) ⇒
    compile_struct_lit f cenv ty fields buf off =
    compile_struct_lit g cenv ty fields buf off
Proof
  Induct >- simp[compile_struct_lit_def] >>
  rpt gen_tac >> rename1 `compile_struct_lit f cenv _ (fld::fields) _ _` >>
  Cases_on `fld` >>
  simp[compile_struct_lit_def] >> rpt strip_tac >>
  fs[] >> simp[lower_value_def]
QED

Theorem compile_attribute_callback_contract:
  expr_callbacks_agree f g cenv [base_e] ⇒
  compile_attribute f cenv ret_ty ty base_e fld =
  compile_attribute g cenv ret_ty ty base_e fld
Proof
  simp[] >> strip_tac >> simp[compile_attribute_def]
QED

Theorem compile_subscript_callback_contract:
  expr_callbacks_agree f g cenv [base_e;idx_e] ⇒
  compile_subscript f cenv ret_ty ty base_e idx_e =
  compile_subscript g cenv ret_ty ty base_e idx_e
Proof
  simp[] >> strip_tac >> simp[compile_subscript_def, lower_value_def]
QED

Theorem compile_acc_callback_contract:
  expr_callbacks_agree f g cenv [e] ⇒
  compile_acc f cenv e item st = compile_acc g cenv e item st
Proof
  simp[] >> strip_tac >>
  Cases_on `item` >> simp[compile_acc_def, lower_value_def]
QED

Theorem lower_value_callback_contract:
  expr_callbacks_agree f g cenv [e] ⇒
  lower_value f cenv ty e = lower_value g cenv ty e
Proof
  simp[] >> strip_tac >> simp[lower_value_def]
QED

Theorem compile_multi_exprs_callback_contract:
  expr_callbacks_agree f g cenv es ⇒
  compile_multi_exprs f cenv es = compile_multi_exprs g cenv es
Proof
  strip_tac >> irule compile_multi_exprs_callback_cong >>
  rpt strip_tac >> drule_all expr_callbacks_agree_apply >> simp[]
QED

Definition call_callback_children_def:
  call_callback_children args default_ret =
    args ++ FLAT (MAP raw_log_topic_exprs args) ++
    (case default_ret of NONE => [] | SOME e => [e])
End

Theorem compile_intcall_callback_contract:
  expr_callbacks_agree f g cenv args ⇒
  compile_call f cenv ret_ty ty (IntCall id) args default_ret st =
  compile_call g cenv ret_ty ty (IntCall id) args default_ret st
Proof
  strip_tac >> drule compile_multi_vvs_callback_contract >>
  simp[compile_call_def]
QED

Theorem compile_send_callback_contract:
  expr_callbacks_agree f g cenv args ⇒
  compile_call f cenv ret_ty ty Send args default_ret st =
  compile_call g cenv ret_ty ty Send args default_ret st
Proof
  Cases_on `args` >- simp[compile_call_def] >>
  rename1 `addr_e::rest` >> Cases_on `rest` >- simp[compile_call_def] >>
  rename1 `addr_e::val_e::tail` >> Cases_on `tail` >>
  simp[compile_call_def] >> strip_tac >> fs[] >>
  simp[lower_value_def, comp_bind_def]
QED

(* msg.data has no expression callback; only the address and value are children. *)
Theorem compile_raw_call_calldata_callback_contract:
  expr_callbacks_agree f g cenv args ⇒
  compile_call f cenv ret_ty ty (RawCallCalldataTarget rcf) args default_ret st =
  compile_call g cenv ret_ty ty (RawCallCalldataTarget rcf) args default_ret st
Proof
  Cases_on `args` >- simp[compile_call_def] >>
  rename1 `addr_e::rest` >> Cases_on `rest` >- simp[compile_call_def] >>
  rename1 `addr_e::value_e::tail` >> Cases_on `tail` >>
  simp[compile_call_def] >> strip_tac >> fs[] >>
  simp[lower_value_def, comp_bind_def]
QED

Theorem compile_extcall_callback_contract:
  expr_callbacks_agree f g cenv (call_callback_children args default_ret) ⇒
  compile_call f cenv ret_ty ty (ExtCall static_call skip_check (fn_name,arg_types,return_type))
    args default_ret st =
  compile_call g cenv ret_ty ty (ExtCall static_call skip_check (fn_name,arg_types,return_type))
    args default_ret st
Proof
  strip_tac >>
  `expr_callbacks_agree f g cenv
     (args ++ (case default_ret of NONE => [] | SOME e => [e]))` by
    fs[call_callback_children_def] >>
  qpat_x_assum `expr_callbacks_agree _ _ _ (call_callback_children _ _)` kall_tac >>
  Cases_on `args` >- simp[compile_call_def] >>
  rename1 `addr_e::rest` >>
  Cases_on `default_ret` >> Cases_on `static_call` >>
  fs[] >>
  Cases_on `rest` >> fs[] >>
  TRY (drule compile_multi_vvs_callback_contract >> strip_tac) >>
  simp[compile_call_def, lower_value_def, comp_bind_def, compile_multi_vvs_def]
QED

Theorem raw_log_topic_exprs_member_bound:
  MEM child (raw_log_topic_exprs e) ==> expr_size child < expr_size e
Proof
  Cases_on `e` >> simp[raw_log_topic_exprs_def] >>
  rename1 `Builtin ann bi es` >> Cases_on `bi` >>
  simp[raw_log_topic_exprs_def, expr_size_def] >>
  strip_tac >> drule expr_list_member_bound >> simp[]
QED

Theorem raw_log_topic_exprs_list_member_bound:
  MEM e args /\ MEM child (raw_log_topic_exprs e) ==>
  expr_size child < list_size expr_size args
Proof
  strip_tac >> drule raw_log_topic_exprs_member_bound >>
  qpat_x_assum `MEM e args` (mp_tac o MATCH_MP expr_list_member_bound) >> simp[]
QED

Theorem expr_callbacks_agree_flat_topics:
  expr_callbacks_agree f g cenv (FLAT (MAP raw_log_topic_exprs args)) /\
  MEM e args ==> expr_callbacks_agree f g cenv (raw_log_topic_exprs e)
Proof
  simp[expr_callbacks_agree_def, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem compile_raw_log_callback_contract:
  expr_callbacks_agree f g cenv args /\
  expr_callbacks_agree f g cenv (FLAT (MAP raw_log_topic_exprs args)) ==>
  compile_call f cenv ret_ty ty RawLog args default_ret st =
  compile_call g cenv ret_ty ty RawLog args default_ret st
Proof
  Cases_on `args` >- simp[compile_call_def] >>
  rename1 `topics_e::rest` >> Cases_on `rest` >- simp[compile_call_def] >>
  rename1 `topics_e::data_e::tail` >> Cases_on `tail` >>
  simp[compile_call_def] >> strip_tac >> fs[] >>
  `expr_callbacks_agree f g cenv (raw_log_topic_exprs topics_e)` by
    metis_tac[expr_callbacks_agree_flat_topics, MEM] >>
  qpat_x_assum `expr_callbacks_agree _ _ _ (raw_log_topic_exprs topics_e)`
    (mp_tac o MATCH_MP compile_multi_exprs_callback_contract) >> strip_tac >>
  simp[lower_value_def, comp_bind_def]
QED

Theorem compile_call_callback_contract:
  expr_callbacks_agree f g cenv (call_callback_children args default_ret) ⇒
  compile_call f cenv ret_ty ty target args default_ret st =
  compile_call g cenv ret_ty ty target args default_ret st
Proof
  strip_tac >> Cases_on `target` >>
  FIRST [irule compile_intcall_callback_contract >>
           fs[call_callback_children_def] >> Cases_on `default_ret` >> fs[],
         irule compile_send_callback_contract >>
           fs[call_callback_children_def] >> Cases_on `default_ret` >> fs[],
         irule compile_raw_call_calldata_callback_contract >>
           fs[call_callback_children_def] >> Cases_on `default_ret` >> fs[],
         irule compile_raw_log_callback_contract >>
           fs[call_callback_children_def],
         rename1 `compile_call f _ _ _ (ExtCall _ _ signature)` >>
           PairCases_on `signature` >>
           irule compile_extcall_callback_contract >> simp[],
         simp[compile_call_def]]
QED

(* ===== Actual child-call edges ===== *)
Theorem call_callback_child_bound:
  MEM child (call_callback_children args default_ret) ⇒
  expr_size child < expr_size (Call ann target args default_ret)
Proof
  Cases_on `default_ret` >> simp[call_callback_children_def] >>
  rpt strip_tac >> gvs[MEM_FLAT, MEM_MAP] >>
  FIRST [drule_all raw_log_topic_exprs_list_member_bound >> simp[expr_size_def] >> NO_TAC,
         drule expr_list_member_bound >> simp[expr_size_def],
         simp[expr_size_def]]
QED

Theorem struct_callback_child_bound:
  MEM child (MAP SND fields) ⇒
  expr_size child < expr_size (StructLit ann nsid fields)
Proof
  simp[MEM_MAP] >> strip_tac >> rename1 `MEM fld fields` >>
  Cases_on `fld` >> gvs[] >> drule expr_struct_field_bound >> simp[]
QED

Theorem expr_list_child_callback_agrees:
  expr_callbacks_agree (expr_child_callback (list_size expr_size args) f) f cenv args
Proof
  irule expr_child_callback_agrees >> simp[expr_list_member_bound]
QED

Theorem lower_value_list_child_call:
  MEM e args ⇒
  lower_value (expr_child_callback (list_size expr_size args) f) cenv ty e =
  lower_value f cenv ty e
Proof
  strip_tac >> irule lower_value_callback_contract >>
  irule expr_child_callback_agrees >> simp[] >>
  drule expr_list_member_bound >> simp[]
QED

Theorem compile_acc_list_child_call:
  MEM e args ⇒
  compile_acc (expr_child_callback (list_size expr_size args) f) cenv e item st =
  compile_acc f cenv e item st
Proof
  strip_tac >> irule compile_acc_callback_contract >>
  irule expr_child_callback_agrees >> simp[] >>
  drule expr_list_member_bound >> simp[]
QED

Theorem compile_multi_exprs_list_child_calls:
  compile_multi_exprs (expr_child_callback (list_size expr_size args) f) cenv args =
  compile_multi_exprs f cenv args
Proof
  irule compile_multi_exprs_callback_contract >>
  irule expr_list_child_callback_agrees
QED

Theorem compile_concat_list_child_calls:
  compile_concat (expr_child_callback (list_size expr_size args) f) cenv args dp infos off =
  compile_concat f cenv args dp infos off
Proof
  irule compile_concat_callback_contract >> irule expr_list_child_callback_agrees
QED

Theorem compile_make_tuple_list_child_calls:
  compile_make_tuple (expr_child_callback (list_size expr_size args) f) cenv args buf off =
  compile_make_tuple f cenv args buf off
Proof
  irule compile_make_tuple_callback_contract >> irule expr_list_child_callback_agrees
QED

Theorem compile_make_array_list_child_calls:
  compile_make_array (expr_child_callback (list_size expr_size args) f) cenv args sz lw (alloc_sz:num) buf idx =
  compile_make_array f cenv args sz lw alloc_sz buf idx
Proof
  irule compile_make_array_callback_contract >> irule expr_list_child_callback_agrees
QED

Theorem compile_subscript_child_calls:
  compile_subscript (expr_child_callback (expr_size (Subscript ann base_e idx_e)) f)
    cenv ret_ty ty base_e idx_e = compile_subscript f cenv ret_ty ty base_e idx_e
Proof
  irule compile_subscript_callback_contract >> irule expr_child_callback_agrees >>
  rw[] >> simp[expr_subscript_child_bounds]
QED

Theorem compile_attribute_child_call:
  compile_attribute (expr_child_callback (expr_size (Attribute ann base_e fld)) f)
    cenv ret_ty ty base_e fld = compile_attribute f cenv ret_ty ty base_e fld
Proof
  irule compile_attribute_callback_contract >> irule expr_child_callback_agrees >>
  simp[expr_attribute_child_bound]
QED

Theorem compile_struct_lit_child_calls:
  compile_struct_lit (expr_child_callback (expr_size (StructLit ann nsid fields)) f)
    cenv ty fields buf off = compile_struct_lit f cenv ty fields buf off
Proof
  irule compile_struct_lit_callback_contract >> irule expr_child_callback_agrees >>
  simp[struct_callback_child_bound]
QED

Theorem compile_call_child_calls:
  compile_call (expr_child_callback (expr_size (Call ann target args default_ret)) f)
    cenv ret_ty ty target args default_ret st =
  compile_call f cenv ret_ty ty target args default_ret st
Proof
  irule compile_call_callback_contract >> irule expr_child_callback_agrees >>
  simp[call_callback_child_bound]
QED

Theorem expr_index_child_bound:
  n < LENGTH args ⇒ expr_size (EL n args) < list_size expr_size args
Proof
  strip_tac >> irule expr_list_member_bound >> simp[EL_MEM]
QED

Theorem expr_head_child_bound:
  args ≠ [] ⇒ expr_size (HD args) < list_size expr_size args
Proof
  Cases_on `args` >> simp[list_size_def]
QED

Theorem nested_array_child_bound:
  MEM (Builtin ann (MakeArray elem_ty bnd) elems) args ∧ MEM e elems ⇒
  expr_size e < list_size expr_size args
Proof
  rpt strip_tac >> imp_res_tac expr_list_member_bound >>
  fs[expr_size_def] >> decide_tac
QED

Theorem is_extcode_characterization:
  ∀src_e. is_extcode src_e ⇔ ∃ann addr. src_e = Attribute ann addr "code"
Proof
  ho_match_mp_tac is_extcode_ind >> simp[is_extcode_def] >>
  rw[] >> gvs[AllCaseEqs()] >> BasicProvers.every_case_tac >> gvs[]
QED

Theorem extcode_child_bound:
  MEM src_e args ∧ is_extcode src_e ⇒
  expr_size (extcode_addr_expr src_e) < list_size expr_size args
Proof
  simp[is_extcode_characterization, PULL_EXISTS] >> rpt strip_tac >> gvs[] >>
  drule expr_list_member_bound >> simp[expr_size_def, extcode_addr_expr_def]
QED

(* Preserved unsuccessful broad probe: splitting the already pattern-completed
   Builtin body duplicates its 83 handoff branches. The small, closed edge
   contracts above/below are the proof interface instead; no theorem from this
   exploratory probe is exported.
Theorem compile_expr_body_guard_transparent:
  ∀f b t cenv ty e st. compile_expr_body
    (expr_child_callback (expr_size e) f)
    (builtin_child_callback (expr_size e) b)
    (type_child_callback (expr_size e) t) cenv ty e st =
  compile_expr_body f b t cenv ty e st
Proof
  rpt gen_tac >> Cases_on `e` >>
  simp[compile_expr_body_def, compile_subscript_child_calls,
       compile_attribute_child_call, compile_struct_lit_child_calls,
       compile_call_child_calls] >>
  simp[lower_value_def, comp_bind_def, expr_size_def] >>
  BasicProvers.every_case_tac >> gvs[expr_size_def]
QED
*)

Theorem builtin_dispatch_child_handoff:
  builtin_child_callback (expr_size (Builtin ann bi args)) b
    cenv ret_ty ty bi args st = b cenv ret_ty ty bi args st
Proof
  simp[expr_size_def]
QED

Theorem type_dispatch_child_handoff:
  type_child_callback (expr_size (TypeBuiltin ann tb ret_ty args)) t
    cenv vv_ty ty tb ret_ty args st = t cenv vv_ty ty tb ret_ty args st
Proof
  simp[expr_size_def]
QED

Theorem ifexp_lower_value_child_calls:
  lower_value (expr_child_callback (expr_size (IfExp ann cond then_e else_e)) f)
    cenv cond_ty cond = lower_value f cenv cond_ty cond ∧
  lower_value (expr_child_callback (expr_size (IfExp ann cond then_e else_e)) f)
    cenv ty then_e = lower_value f cenv ty then_e ∧
  lower_value (expr_child_callback (expr_size (IfExp ann cond then_e else_e)) f)
    cenv ty else_e = lower_value f cenv ty else_e
Proof
  simp[lower_value_def, FUN_EQ_THM, comp_bind_def, expr_size_def]
QED

Theorem compile_multi_vvs_call_children:
  compile_multi_vvs (expr_child_callback (expr_size (Call ann target args default_ret)) f)
    cenv args = compile_multi_vvs f cenv args
Proof
  irule compile_multi_vvs_callback_contract >> irule expr_child_callback_agrees >>
  rpt strip_tac >> drule expr_list_member_bound >> simp[expr_size_def]
QED

Theorem compile_multi_exprs_nested_array_children:
  MEM (Builtin ann (MakeArray elem_ty bnd) elems) args ⇒
  compile_multi_exprs (expr_child_callback (list_size expr_size args) f) cenv elems =
  compile_multi_exprs f cenv elems
Proof
  strip_tac >> irule compile_multi_exprs_callback_contract >>
  irule expr_child_callback_agrees >> rpt strip_tac >>
  drule_all nested_array_child_bound >> simp[]
QED

Theorem lower_value_extcode_child:
  MEM src_e args ∧ is_extcode src_e ⇒
  lower_value (expr_child_callback (list_size expr_size args) f)
    cenv ty (extcode_addr_expr src_e) =
  lower_value f cenv ty (extcode_addr_expr src_e)
Proof
  strip_tac >> irule lower_value_callback_contract >>
  irule expr_child_callback_agrees >> simp[] >>
  drule_all extcode_child_bound >> simp[]
QED

val _ = List.app (fn (_,th) =>
  if null (List.filter (fn s => s <> "DISK_THM") (fst (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail "callback contract oracle dependency")
  (DB.thms "exprCallbackContracts");
