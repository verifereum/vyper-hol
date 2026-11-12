(* Allocation-frontier capacity for a selected framed array element. *)
Theory bodyMemSubscriptArrayBounds
Ancestors
  exprSimMemDefs exprSimAttributeProps exprSimDefs exprSimProps loweringPosts
  exprLowering compileEnv context vyperAST vyperValue valueEncoding
  valueEncodingDefs valueTypingMemoryProps words integer arithmetic

Theorem array_selected_store_bound_mem:
  vv_post ctx func cenv cx (Subscript et obj idx) es sa sb s0 ee child
    (LocatedValue et (mk_ptr dst (vv_loc bvv))) u /\
  vv_store_bound cx (ArrayT et bd) lt eb tv bvv t /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx tv eb = (INL (ArrayV av), eb) /\
  eval_operand (vv_operand bvv) t = SOME w /\
  (vv_loc bvv = LocMemory ==> ?n. bd = Fixed n /\ Num i < n) /\
  eval_operand dst u = SOME
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
                Num i * type_memory_size etv)) /\
  t.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_alloca_next < dimword (:256) ==>
  vv_store_bound cx et et ee child
    (LocatedValue et (mk_ptr dst (vv_loc bvv))) u
Proof
  strip_tac >> Cases_on `vv_loc bvv = LocMemory`
  >- (fs[] >> gvs[] >>
      `type_memory_size (ArrayTV etv (Fixed n)) = 0 \/
       w2n w + type_memory_size (ArrayTV etv (Fixed n)) <= t.vs_alloca_next` by
        (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _`
          (mp_tac o CONJUNCT1 o REWRITE_RULE [vv_store_bound_def]) >>
         Cases_on `bvv` >>
         gvs[vv_loc_def, vv_location_def, vv_operand_def, is_word_type_def,
             val_store_size_def, type_memory_size_def] >> metis_tac[]) >>
      `Num i * type_memory_size etv + type_memory_size etv <=
       n * type_memory_size etv` by
        (`(Num i + 1) * type_memory_size etv <= n * type_memory_size etv` by
           (irule LESS_MONO_MULT >> decide_tac) >>
         qpat_x_assum `(_ + 1) * _ <= _` mp_tac >>
         pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
      `type_memory_size etv = 0 \/
       w2n (w + n2w (Num i * type_memory_size etv)) +
         type_memory_size etv <= u.vs_alloca_next` by
        (Cases_on `type_memory_size etv = 0` >> simp[] >>
         `w2n (w + n2w (Num i * type_memory_size etv)) =
          w2n w + Num i * type_memory_size etv` by
           (irule field_ptr_w2n >>
            qexistsl_tac [`type_memory_size etv`, `n * type_memory_size etv`] >>
            gvs[type_memory_size_def] >> decide_tac) >>
         gvs[type_memory_size_def] >> decide_tac) >>
      drule vv_store_bound_capacity >>
      simp[expr_type_def, post_value_type_def, mk_ptr_def] >>
      disch_then irule >> simp[] >> metis_tac[]) >>
  irule vv_store_bound_nonmem >> simp[mk_ptr_def]
QED
