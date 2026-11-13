Theory ctorEntryLocals
Ancestors
  entryLocals compileVyper compileEnv loweringStateRelDefs moduleLowering context
  exprLoweringProps list finite_map
Libs
  monadsyntax

Theorem compile_fixed_region_with_id_reserved_operand[local]:
  !cap st id buf st'.
    compile_fixed_region_with_id cap st = ((id, buf), st') ==>
    ?x. buf.buf_operand = Var x /\ not_fresh_at st' x
Proof
  rpt strip_tac >> drule compile_fixed_region_with_id_result >> strip_tac >>
  simp[] >> simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

(* The actual deployment prefix reserves immutables before registering
   arguments; the packaged constructor still has no immutable base. *)
Theorem constructor_reserved_entry_locals:
  !tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
   cenv0 pos_args rest cap data_size st0 imm st1 cenv st2.
    package_constructor tops use_trans nkey_map
      (mut, nr, rr, fname, fargs, dflts, ret, fbody) =
      (cenv0, pos_args, rest) /\
    (if cap > 0 then
       do r <- compile_fixed_region_with_id cap;
          comp_return (SND r).buf_operand
       od
     else comp_return (Lit 0w)) st0 = (imm, st1) /\
    compile_register_constructor_args
      (cenv0 with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
      pos_args 0 data_size st1 = (cenv, st2) ==>
    local_ptrs_reserved cenv st2 /\
    EVERY (\a. ?p sz.
      FLOOKUP cenv.ce_vars (FST a) = SOME (PtrVar (Var p) sz)) fargs /\
    cenv.ce_is_ctor /\
    cenv.ce_imm_alloca = (if cap > 0 then SOME imm else NONE) /\
    (cap > 0 ==> ?x. imm = Var x /\
      not_fresh_at st1 x /\ not_fresh_at st2 x)
Proof
  rpt gen_tac >> strip_tac >>
  `cenv0.ce_vars = (build_compile_env tops Deploy mut fname fargs ret fbody
                      use_trans).ce_vars /\
   pos_args = build_positional_args cenv0 fargs /\ cenv0.ce_is_ctor` by
    gvs[package_constructor_def, update_cenv_nonreentrant_def] >>
  `cap > 0 ==> ?x. imm = Var x /\ not_fresh_at st1 x` by
    (strip_tac >>
     qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
     simp[comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     rename1 `compile_fixed_region_with_id cap st0 = (r, sa)` >>
     PairCases_on `r` >>
     drule compile_fixed_region_with_id_reserved_operand >> simp[]) >>
  drule compile_register_constructor_args_fields >> simp[] >> strip_tac >>
  qspecl_then [`tops`, `Deploy`, `mut`, `fname`, `fargs`, `ret`, `fbody`,
               `use_trans`] strip_assume_tac build_compile_env_vars >>
  drule compile_register_constructor_args_reserved >>
  impl_tac >- (simp[build_positional_args_FST] >>
              Cases_on `cap > 0` >> gvs[] >> metis_tac[]) >>
  strip_tac >> simp[] >> conj_tac
  >- (simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >>
      gvs[MEM_MAP] >> metis_tac[]) >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[local_ptrs_reserved_def]
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then
       print ("CTOR_ENTRY_KERNEL_CLOSED " ^ name ^ "\n")
     else raise Fail ("Unclosed constructor entry theorem: " ^ name)
  end) (DB.thms "ctorEntryLocals");
