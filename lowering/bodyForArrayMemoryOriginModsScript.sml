(* Save the selected memory origin at length acquisition, before header install. *)
Theory bodyForArrayMemoryOriginMods
Ancestors
  bodyForArrayOriginMods bodyForArrayHeldInstallRouteMods
  bodyPtrDefs bodyFullTargetArrayLoad exprSimCopy
  exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeEvalStoragePreservation vyperTypeValues vyperTypeInvariants
  loweringPosts loweringStateRelDefs venomState vyperState compileEnv
  context vyperTypeExprSoundness words finite_map arithmetic

Theorem owned_length_row[local]:
  vv_own c cx (ArrayT sty bd) sa0 sbExpr em (Value (ArrayV av)) vv r /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  evaluate_type (get_tenv cx) (ArrayT sty bd) = SOME (ArrayTV tv bd) /\
  copy_old_operand sbExpr (vv_operand vv) /\
  local_ptrs_reserved c sbExpr /\
  array_length_frame sbExpr r Gr traw u Gu tu /\
  eval_operand (vv_operand vv) u = SOME bw /\
  0 < type_memory_size (ArrayTV tv bd) ==>
  ?aid b sz. aid < sbExpr.cs_next_id /\
    FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
    b <= w2n bw /\
    w2n bw + type_memory_size (ArrayTV tv bd) <= b + sz /\
    (!nm lb lsz. local_region c em.scopes u nm lb lsz ==>
      b + sz <= lb \/ lb + lsz <= b)
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `array_length_frame _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [array_length_frame_def]) >>
  `u.vs_labels = r.vs_labels /\ u.vs_allocas = r.vs_allocas` by
    (qpat_assum `(_ with vs_vars := _) = r` (once_rewrite_tac o single o SYM) >> simp[]) >>
  `eval_operand (vv_operand vv) r = SOME bw` by
    (Cases_on `vv_operand vv` >> gvs[copy_old_operand_def,eval_operand_def]) >>
  `!nm lb lsz. local_region c em.scopes u nm lb lsz <=>
               local_region c em.scopes r nm lb lsz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     fs[local_ptrs_reserved_def] >>
     `not_fresh_at sbExpr p` by
       (qpat_assum `!n1 n2 p sz1 sz2. _` (drule_then strip_assume_tac) >> simp[]) >>
     qpat_assum `!x. not_fresh_at _ x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  Cases_on `vv` >>
  gvs[vv_location_def,vv_operand_def,vv_own_def,expr_val_own_def,
      read_result_def,return_def,is_word_type_def,val_footprint_def] >>
  qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem held_origin_place_type[local]:
  expr_body_pre_mods mods c cx env e start /\
  eval_expr cx e start = (INL (PlaceR (MemoryPlace name path)),em) /\
  expr_type e = ArrayT sty bd /\
  evaluate_type (get_tenv cx) (ArrayT sty bd) = SOME (ArrayTV tv bd) ==>
  runtime_place_typed cx em (MemoryPlace name path) (ArrayTV tv bd)
Proof
  strip_tac >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  drule_all_then strip_assume_tac eval_expr_success_storage_facts >>
  `env.type_defs = get_tenv cx` by
    fs[runtime_consistent_def,env_consistent_def,env_context_consistent_def] >>
  qpat_x_assum `eval_result_typed _ _ _` mp_tac >>
  simp[eval_result_typed_def]
QED

(* The two clauses are for the Owned and Held callback branches respectively.
   Neither asks for an installed header or fixes its destination word. *)
Theorem for_array_memory_origin_mods:
  (evaluate_type (get_tenv cx) (ArrayT sty bd) = SOME (ArrayTV tv bd) /\
   value_has_type (ArrayTV tv bd) (ArrayV av) /\
   vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
   vv_own c cx (ArrayT sty bd) sa0 sbExpr em (Value (ArrayV av)) vv r /\
   (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
   copy_old_operand sbExpr (vv_operand vv) /\
   local_ptrs_reserved c sbExpr /\
   array_length_frame sbExpr r Gr traw u Gu tu /\
   eval_operand (vv_operand vv) u = SOME bw /\
   ptr_mem_ok cx (ArrayT sty bd) (ArrayV av) (vv_operand vv) Gu tu u ==>
   !dw. for_array_origin_mods c cx lo (sty,bd,LocMemory)
      (em,sbExpr,u,Gu,tu) (vv_operand vv,bw) vs
      ((em,u,Gu,tu,dw,bw,ForArrayOwned av),SOME av)) /\
  (expr_body_pre_mods mods c cx env e start /\
   eval_expr cx e start = (INL (PlaceR (MemoryPlace name path)),em) /\
   expr_type e = ArrayT sty bd /\
   expr_sim_inv_mods mods c cx env em /\
   evaluate_type (get_tenv cx) (ArrayT sty bd) = SOME (ArrayTV tv bd) /\
   vv_post_mods H ctx func c cx e es sa0 sbExpr s0 em
     (PlaceR (MemoryPlace name path)) (LocatedValue ann p) r /\
   MEM tgt (expr_places e) /\ place_access tgt [] = (NameTarget name,attrs) /\
   path = MAP AttrSubscript attrs ++ tail /\
   value_has_type (ArrayTV tv bd) (ArrayV av) /\
   vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
   read_result cx (PlaceR (MemoryPlace name path)) em = (INL (ArrayV av),em) /\
   copy_old_operand sbExpr p.ptr_operand /\
   local_ptrs_reserved c sbExpr /\ local_ptrs_reserved c saL /\
   array_length_frame sbExpr r Gr traw u Gu tu /\
   eval_operand p.ptr_operand u = SOME bw /\
   ptr_mem_ok cx (ArrayT sty bd) (ArrayV av) p.ptr_operand Gu tu u ==>
   (?ent q sz rw delta. lookup_scopes name em.scopes = SOME ent /\
     read_memory_path ent path = INL (ArrayV av) /\
     FLOOKUP c.ce_vars name = SOME (PtrVar (Var q) sz) /\
     lookup_var q u = SOME rw /\ not_fresh_at saL q /\
     mem_path_offset ent.type path = SOME (delta,ArrayTV tv bd) /\
     bw = rw + n2w delta /\ w2n rw + delta < dimword (:256) /\
     w2n rw <= w2n bw /\ w2n bw + type_memory_size (ArrayTV tv bd) <= w2n rw + sz) /\
   (?tgt attrs tail. MEM tgt (expr_places e) /\
     place_access tgt [] = (NameTarget name,attrs) /\
     path = MAP AttrSubscript attrs ++ tail) /\
   (!dw. for_array_origin_mods c cx lo (sty,bd,LocMemory)
      (em,sbExpr,u,Gu,tu) (p.ptr_operand,bw) vs
      ((em,u,Gu,tu,dw,bw,ForArrayHeld name path av),SOME av)))
Proof
  conj_tac >- suspend "owned" >> suspend "held"
QED

Resume for_array_memory_origin_mods[owned]:
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >> gen_tac >>
  `!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
     val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) mem` by
    (qpat_assum `ptr_mem_ok _ _ _ _ _ _ _`
       (qspecl_then [`ArrayTV tv bd`,`bw`] mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
     simp[]) >>
  `evaluate_type (get_tenv cx) sty = SOME tv` by
    (drule evaluate_type_ArrayT_cases >> simp[]) >>
  simp[for_array_origin_mods_def] >>
  strip_tac >> drule_all owned_length_row >> simp[]
QED

Resume for_array_memory_origin_mods[held]:
  strip_tac >>
  conj_tac
  >- (drule_all_then assume_tac held_origin_place_type >>
      drule_all_then strip_assume_tac for_array_held_length_root_mods >>
      `read_memory_path ent path = INL (ArrayV av)` by
        (Cases_on `read_memory_path ent path` >>
         fs[read_result_def,read_place_def,bind_def,get_scopes_def,
            lift_option_type_def,lift_sum_def,return_def,raise_def]) >>
      qexistsl_tac [`ent`,`q`,`sz`,`rw`,`delta`] >> simp[]) >>
  conj_tac >- (qexistsl_tac [`tgt`,`attrs`,`tail`] >> simp[]) >>
  `evaluate_type (get_tenv cx) sty = SOME tv` by
    (drule evaluate_type_ArrayT_cases >> simp[]) >>
  qpat_x_assum `path = MAP AttrSubscript _ ++ _` kall_tac >>
  simp[for_array_origin_mods_def]
QED

Finalise for_array_memory_origin_mods
