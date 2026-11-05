Theory bodyIntCallAggregateCopy
Ancestors
  exprSimCopy exprSimStorageCopy venomState exprLowering compileEnv
  exprLoweringProps localPtrsProps loweringSlice loweringPosts valueEncoding
  valueEncodingProps vyperValue vyperValueOperation context freshWrites
  venomInst words finite_map fragExec exprSimAlloc storageDecodeMemory

(* copy_static hides only registers, memory and execution position.
   Contract observations therefore project from its exact equality. *)
Theorem copy_static_contract_storage:
  copy_static t = copy_static s ==>
  contract_storage t = contract_storage s
Proof
  strip_tac >>
  `contract_storage (copy_static t) = contract_storage (copy_static s)` by simp[] >>
  qpat_x_assum `copy_static _ = copy_static _` kall_tac >>
  gvs[copy_static_def, contract_storage_def]
QED

Theorem copy_static_contract_transient:
  copy_static t = copy_static s ==>
  contract_transient t = contract_transient s
Proof
  strip_tac >>
  `contract_transient (copy_static t) = contract_transient (copy_static s)` by simp[] >>
  qpat_x_assum `copy_static _ = copy_static _` kall_tac >>
  gvs[copy_static_def, contract_transient_def]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Copy observations have unproved dependencies"
  end) [copy_static_contract_storage, copy_static_contract_transient];

Theorem unwrap_storage_copy_storage_frame_frag:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R s1.
    unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ~is_word_type t /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
       type_memory_bytes cenv t = type_memory_size tvt /\ type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s1 ==>
    frag_exec ctx sm sb (\s. s = s1)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
           contract_storage s = contract_storage s1 /\
           contract_transient s = contract_transient s1) R
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  `compile_ensure_in_memory p.ptr_operand p.ptr_location
     (type_memory_bytes cenv t) ((type_memory_bytes cenv t + 31) DIV 32)
     cenv.ce_is_ctor cenv.ce_imm_alloca sm = (op,sb)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[unwrap_value_def]) >>
  qpat_x_assum `unwrap_value _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ _ = _` mp_tac >>
  drule ensure_storage_memory_layout >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gnvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  rename1 `fn_has_code sm sf func` >> suspend "allocation"
QED

Resume unwrap_storage_copy_storage_frame_frag[allocation]:
  `t = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
  `?a. eval_operand p.ptr_operand s1 = SOME a /\
       storage_holds cx (p.ptr_location = LocTransient)
         (expr_type e) (Value v) a es' s1` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[vv_post_def, vv_holds_def]) >>
  `cs_extends sm mid` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends mid sf` by
    (irule storage_copy_suffix_extends >>
     qexistsl [`buf.buf_operand`, `p.ptr_location`,
       `(type_memory_bytes cenv t + 31) DIV 32`, `p.ptr_operand`, `()`] >>
     gvs[comp_ignore_bind_def]) >>
  `fn_has_code sm mid func` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx es' s1` by gvs[vv_post_def] >>
  `?tv. evaluate_type (get_tenv cx) t = SOME tv` by
    (gvs[storage_holds_def] >> metis_tac[]) >>
  `type_memory_bytes cenv t = type_memory_size tv /\
   type_memory_size tv < 2 ** 64` by
    (first_x_assum (qspec_then `tv` mp_tac) >> simp[]) >>
  `type_memory_size tv < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  `type_memory_bytes cenv t < dimword (:256)` by metis_tac[] >>
  drule_all alloc_buffer_source_frag >>
  disch_then (qspec_then `R` strip_assume_tac) >>
  suspend "suffix"
QED

Resume unwrap_storage_copy_storage_frame_frag[suffix]:
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv t`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid sf` by
    (irule storage_copy_suffix_ci_mono >>
     qexistsl [`buf.buf_operand`, `p.ptr_location`,
       `(type_memory_bytes cenv t + 31) DIV 32`, `p.ptr_operand`, `()`] >>
     gvs[comp_ignore_bind_def]) >>
  `sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= sf.cs_next_id` by
    gvs[ci_mono_def] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
       [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `((type_memory_bytes cenv t + 31) DIV 32) = type_slot_size tv` by
    (simp[type_memory_size_slots] >> decide_tac) >>
  `!x. p.ptr_operand = Var x \/ buf.buf_operand = Var x ==>
       not_fresh_at mid x` by
    (rpt strip_tac >> gvs[] >> metis_tac[not_fresh_at_mono]) >>
  `(type_memory_bytes cenv t + 31) DIV 32 < 2 ** 256 /\
   w2n w + 32 * ((type_memory_bytes cenv t + 31) DIV 32) < 2 ** 256` by
    (fs[type_memory_size_slots, wordsTheory.dimword_def] >> decide_tac) >>
  qpat_assum `frag_exec ctx sm mid _ _ R` (mp_then Any mp_tac frag_exec_then) >>
  disch_then irule >> simp[] >>
  `storage_holds cx (p.ptr_location = LocTransient) t (Value v) a es' s1` by metis_tac[] >>
  `storage_holds cx (p.ptr_location = LocTransient) t (Value v) a es' u` by
    (qpat_x_assum `storage_holds _ _ _ _ _ es' s1` mp_tac >> simp[storage_holds_def]) >>
  drule_all (REWRITE_RULE[comp_ignore_bind_def] storage_copy_suffix_value_frag) >>
  disch_then (qspec_then `R` mp_tac) >>
  disch_then (mp_then Any mp_tac frag_exec_conseq) >>
  disch_then irule >> simp[] >> gen_tac >> strip_tac >>
  conj_tac >- suspend "semantic_post" >>
  metis_tac[copy_static_contract_storage, copy_static_contract_transient]
QED

Resume unwrap_storage_copy_storage_frame_frag[semantic_post]:
  irule copy_buffer_post_transport >>
  qpat_assum `t = expr_type e` (fn th => rewrite_tac[GSYM th]) >>
  simp[] >> goal_assum (drule_at Any) >>
  simp[mk_inst_def, SF SFY_ss] >>
  qexists `mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
       [STRING #"%" (toString sm.cs_next_var)]` >>
  qexistsl [`mid`, `s1`, `sm`, `u`, `LocatedValue t p`] >>
  simp[mk_inst_def] >> gnvs[] >> metis_tac[]
QED

Finalise unwrap_storage_copy_storage_frame_frag

val _ =
  let val th = unwrap_storage_copy_storage_frame_frag
      val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Storage copy forcing has unproved dependencies"
  end;
