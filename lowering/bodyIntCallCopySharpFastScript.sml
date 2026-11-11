Theory bodyIntCallCopySharpFast
Ancestors
  placeMemoryTypedPrimitive placeMemoryTypedBase placeMemoryPrimitiveForward
  context compileEnv emitHelper exprLoweringProps venomState valueEncodingProps

Theorem typed_memory_sarray_fast_forward_sharp:
  ~is_abi_dynamic cenv.ce_struct_fields det /\
  type_widens_to tenv (ArrayT src_et (Fixed m)) (ArrayT det (Fixed n)) /\
  compile_copy_sarray_typed cenv dst det src src_et n sa = ((),sb) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv (ArrayT src_et (Fixed m)) = SOME stv /\
  evaluate_type tenv (ArrayT det (Fixed n)) = SOME dtv /\
  val_wf dtv v /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_bytes cenv (ArrayT det (Fixed n)) = type_memory_size dtv /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `ArrayT src_et (Fixed m) = ArrayT det (Fixed n)` by
    (irule (INST_TYPE [``:'a`` |-> ``:string``, ``:'b`` |-> ``:num``]
              typed_memory_static_widening) >> conj_tac
     >- (qexists_tac `cenv.ce_struct_fields` >> simp[is_abi_dynamic_def]) >>
     qexists_tac `tenv` >> simp[]) >>
  gvs[] >>
  `compile_copy_memory dst src (type_memory_size dtv) sa = ((),sb)` by
    (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def] >>
     gvs[type_memory_bytes_def]) >>
  `type_memory_size dtv < dimword (:256)` by decide_tac >>
  drule_all compile_copy_memory_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (irule valueEncodingPropsTheory.val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`s.vs_memory`, `type_memory_size dtv`, `w2n sw`] >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `_ = s` mp_tac >> simp[venom_state_component_equality]) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
