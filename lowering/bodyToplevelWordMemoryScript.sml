(* Bounded forced word consumers; aggregate and constructor immutables remain residual. *)
Theory bodyToplevelWordMemory
Ancestors
  bodyToplevelMemory bodyUnwrapMemory bodyMemoryDefs exprSimUnwrap exprSim
  exprLowering exprLoweringProps compileEnv context fragExecMem fragExec
  vyperAST vyperValue vyperInterpreter vyperState loweringSlice exprSimLeaves
  exprSimHyps accountsRelProps vyperTypeGlobalLookupSoundness vyperTypeSystem

Theorem body_unwrap_location_word_mem[local]:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
   (p.ptr_location = LocCode /\ ~cenv.ce_is_ctor)) /\ is_word_type t /\
  read_result cx raw es' = (INL v,es') /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' raw (LocatedValue t p) s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s) R
Proof
  strip_tac >> (drule vv_post_read_result >> strip_tac >>
  irule frag_exec_mem_conseq >>
  qexistsl [`\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
                         (LocatedValue t p) s /\
                 s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s`,
            `\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
                 s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s`, `R`] >>
  simp[] >>
  Cases_on `p.ptr_location = LocCode`
  >- (irule unwrap_runtime_immutable_word_sim_mem >>
      gvs[unwrap_value_def, compile_ptr_load_def, compile_imm_load_word_def]) >>
  irule unwrap_storage_word_sim_mem >> simp[] >> metis_tac[])
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag body_unwrap_location_word_mem)
  in if null axioms andalso null (Thm.hyp body_unwrap_location_word_mem) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_TOPLEVEL_WORD_MEMORY_AUDIT OK\n"
     else raise Fail "toplevel word memory inherited admission"
  end;

Theorem body_location_word_sim_mem[local]:
  expr_vv_sim_mem ctx func cenv cx ty e es /\
  (storage_vars_rel cenv cx /\ transient_vars_rel cenv cx ==>
    !sa. ?p. compile_expr cenv ty e sa = (LocatedValue (expr_type e) p,sa) /\
      (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
       (p.ptr_location = LocCode /\ ~cenv.ce_is_ctor))) /\
  is_word_type (expr_type e) ==>
  expr_sim_mem ctx func cenv cx ty e es
Proof
  strip_tac >> simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  irule frag_exec_mem_pointwise >> rw[] >> gvs[] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `_ ==> !sa. _` drule_all >>
  disch_then (qspec_then `sa` strip_assume_tac) >> (
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >> strip_tac >>
  `cs_extends sa sb` by metis_tac[unwrap_value_extends] >>
  `fn_has_code sa sa func` by metis_tac[fn_has_code_split, cs_extends_refl] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw,est)` >>
  qpat_x_assum `(do result <- _; _ od) _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `raw`
  >- (rename1 `eval_expr _ _ _ = (INL r,est)` >> simp[] >> strip_tac >>
      drule read_result_state >> strip_tac >> gvs[] >>
      `expr_vv_res_ok (INL r)` by
        (Cases_on `r` >> gvs[expr_vv_res_ok_def, read_result_def,
                             raise_def, expr_res_ok_def]) >>
      `(INL r : eval_result + exception) <>
        INR (Error (RuntimeError "convert empty bytes to signed"))` by simp[] >>
      qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
        (assume_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
      first_x_assum drule_all >> disch_then (qspec_then `s0` assume_tac) >>
      irule frag_exec_mem_seq_pointwise >>
      qexistsl [`\s. vv_post ctx func cenv cx e es sa sa s0 es' r
                    (LocatedValue (expr_type e) p) s /\
                    s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s`, `sa`] >>
      simp[cs_extends_refl] >> reverse conj_tac
      >- (irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >>
          simp[expr_exit_def]) >>
      gen_tac >> strip_tac >> Cases_on `res`
      >- (irule frag_exec_mem_conseq >>
          qexistsl [`\s. vv_post ctx func cenv cx e es sa sa s0 es' r
                           (LocatedValue (expr_type e) p) s /\
                         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s`,
                    `\s. expr_post ctx func cenv cx e es sa sb s0 es' x op s /\
                         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s`,
                    `expr_exit (INL x)`] >> simp[] >>
          irule body_unwrap_location_word_mem >> simp[]) >>
      drule vv_post_failed_read >> metis_tac[]) >>
  rename1 `eval_expr _ _ _ = (INR exc,est)` >> strip_tac >> gvs[] >>
  `expr_vv_res_ok (INR exc)` by gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
  `(INR exc : eval_result + exception) <>
   INR (Error (RuntimeError "convert empty bytes to signed"))` by simp[] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (assume_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  first_x_assum drule_all >> disch_then (qspec_then `s0` assume_tac) >>
  `expr_exit (INR exc : eval_result + exception) =
   expr_exit (INR exc : value + exception)` by
    simp[FUN_EQ_THM, expr_exit_exception_transport] >> fs[] >>
  `frag_exec_mem ctx sa sa (\s. s = s0) (\s. F)
     (expr_exit (INR exc : value + exception))` by
    (irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >>
     simp[expr_exit_exception_transport]) >>
  irule frag_exec_mem_exit_prefix >> qexists_tac `sa` >> simp[cs_extends_refl])
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag body_location_word_sim_mem)
  in if null axioms andalso null (Thm.hyp body_location_word_sim_mem) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_LOCATION_WORD_MEMORY_AUDIT OK\n"
     else raise Fail "located word consumer inherited admission"
  end;
