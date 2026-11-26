(* Qualified immutable element domain and compiler-shape normalization. *)
Theory bodyForArraySnapshotCodeDomainMods
Ancestors
  bodyFullForImmutableElementInput bodyForArraySnapshotChildMods
  whitelistForIterImmCopy stmtLowering compileEnv
  bodyFullPredsMods bodyFullPostsMods loweringPosts exprLoweringProps
  valueEncodingProps arithmetic words list finite_map
Libs
  monadsyntax

Theorem snapshot_code_copy_shape[local]:
  compile_iter_elem_copy c (Var out) (Var xd) stride LocCode F dty sty sa =
    ((),sb) /\
  (stride = 32 \/ ?q. stride = 32*q /\ 32 < stride) ==>
  ?q. stride = 32*q /\
    compile_imm_copy_to_memory c.ce_is_ctor c.ce_imm_alloca
      (Var out) (Var xd) q 0 sa = ((),sb)
Proof
  strip_tac
  >- (qexists_tac `SUC 0` >> conj_tac
      >- simp[]
      >> qpat_x_assum `stride = 32` SUBST_ALL_TAC >>
         qpat_assum `compile_iter_elem_copy c (Var out) (Var xd) 32 LocCode F dty sty sa =
           ((),sb)` mp_tac >>
         simp[whitelistForIterImmCopyTheory.immutable_iter_small_copy,
              contextTheory.compile_imm_copy_to_memory_def,
              contextTheory.compile_lit_byte_offset_def, comp_bind_def,
              comp_return_def, comp_ignore_bind_def, NoAsms] >>
         pairarg_tac >> gvs[] >> pairarg_tac >> gvs[])
  >> (qexists_tac `q` >> conj_tac
      >- first_assum ACCEPT_TAC
      >> qpat_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` mp_tac >>
         simp[immutable_iter_large_copy] >>
         qpat_x_assum `stride = 32 * q` SUBST_ALL_TAC >>
         gvs[immutable_iter_large_copy, ADD_DIV_ADD_DIV])
QED
Theorem for_array_snapshot_code_domain_mods:
  supported_stmt (main_module mods) bindings
      (For id fty (Array e) n loop_body) /\
  expr_sim_inv_mods mods c cx env es /\
  post_value_type c e = expr_type e /\ arr_ty = expr_type e /\
  arr_elem_ty = (case arr_ty of ArrayT et _ => et | _ => fty) /\
  evaluate_type (get_tenv cx) arr_ty = SOME (ArrayTV tv bd) /\
  immutable_holds c cx (post_value_type c e) rv bw es s /\
  read_result cx rv es = (INL (ArrayV av),es) /\
  vs = MAP Value (array_elements (ArrayTV tv bd) av) /\ k < LENGTH vs /\
  stride = elem_size_in_location c LocCode arr_elem_ty /\
  header = (case bd of Fixed _ => 0 | Dynamic _ => 32) /\
  lookup_var out s = SOME (bw + n2w (header + k * stride)) /\
  not_fresh_at sa out /\
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list) ctx func c cx es s /\
  ghost_inv_at D lo d c cx es G tn s /\
  (c.ce_is_ctor ==> w2n bw + type_memory_size (ArrayTV tv bd) <= lo) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dst,capacity) /\
  stride <= capacity /\
  (!region x. c.ce_imm_alloca = SOME region /\ region = Var x ==>
    not_fresh_at sa x) /\
  op_taint tn (Var out) = {} /\ op_prov G (Var out) = NONE /\
  compile_iter_elem_copy c (Var out) (Var xd) stride LocCode F dty sty sa =
    ((),sb) ==>
  arr_ty = ArrayT fty bd /\ arr_elem_ty = fty /\
  evaluate_type (get_tenv cx) fty = SOME tv /\
  stride = type_memory_size tv /\
  (stride = 32 \/ ?q. stride = 32*q /\ 32 < stride) /\
  w2n dst + capacity < dimword (:256) /\
  ?q. stride = 32*q /\
    compile_imm_copy_to_memory c.ce_is_ctor c.ce_imm_alloca
      (Var out) (Var xd) q 0 sa = ((),sb) /\
  ?v a. EL k vs = Value v /\ value_has_type tv v /\ val_wf tv v /\
    immutable_holds c cx fty (Value v) a es s /\
    eval_operand (Var out) s = SOME a /\
    copy_old_operand sa (Var out) /\ op_taint tn (Var out) = {} /\
    w2n a = w2n bw + header + k * stride /\
    w2n dst + stride <= s.vs_alloca_next /\
    (c.ce_is_ctor ==>
      op_prov G (Var out) = NONE /\
      w2n a + stride <= lo /\ lo <= w2n dst /\
      w2n a + stride <= s.vs_alloca_next /\
      loweringStateRelDefs$regions_disjoint (w2n a) stride (w2n dst) stride /\
      !region. c.ce_imm_alloca = SOME region ==>
        eval_operand region s = SOME 0w /\ copy_old_operand sa region /\
        op_taint tn region = {} /\ op_prov G region = NONE) /\
    (~c.ce_is_ctor ==>
      w2n a + stride <= LENGTH s.vs_data_section /\
      w2n a + stride < dimword (:256))
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm
    (fn th => map_every assume_tac (CONJUNCTS th)))
    `arr_ty = ArrayT fty bd /\ arr_elem_ty = fty /\
     evaluate_type (get_tenv cx) fty = SOME tv /\
     stride = type_memory_size tv /\
     (stride = 32 \/ ?q. stride = 32*q /\ 32 < stride) /\
     w2n dst + capacity < dimword (:256) /\
     ?v a. EL k vs = Value v /\ value_has_type tv v /\ val_wf tv v /\
       immutable_holds c cx fty (Value v) a es s /\
       eval_operand (Var out) s = SOME a /\ copy_old_operand sa (Var out) /\
       op_taint tn (Var out) = {} /\
       w2n a = w2n bw + header + k * stride /\
       w2n dst + stride <= s.vs_alloca_next /\
       (c.ce_is_ctor ==> op_prov G (Var out) = NONE /\
         w2n a + stride <= lo /\ lo <= w2n dst /\
         w2n a + stride <= s.vs_alloca_next /\
         loweringStateRelDefs$regions_disjoint (w2n a) stride (w2n dst) stride /\
         !region. c.ce_imm_alloca = SOME region ==>
           eval_operand region s = SOME 0w /\ copy_old_operand sa region /\
           op_taint tn region = {} /\ op_prov G region = NONE) /\
       (~c.ce_is_ctor ==> w2n a + stride <= LENGTH s.vs_data_section /\
         w2n a + stride < dimword (:256))`
  >- (irule (Q.INST [`bytes` |-> `stride`] (INST_TYPE [alpha |-> ``:256``]
          for_immutable_element_copy_input_mods)) >>
      rpt conj_tac >> TRY (metis_tac[]) >>
      TRY (qpat_assum `!region x. c.ce_imm_alloca = SOME region /\ region = Var x ==>
        not_fresh_at sa x` ACCEPT_TAC) >>
      qexistsl_tac [`H`,`ctx`,`func`] >> first_assum ACCEPT_TAC >>
      TRY (metis_tac[])) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  drule_all snapshot_code_copy_shape >> metis_tac[]
QED
