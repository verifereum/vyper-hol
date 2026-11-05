(* Parallel PHI values and annotations are read from the original inputs. *)
Theory o1LowerDloadPhi
Ancestors
  o1LowerDloadEnvironment o1LowerDloadOpaque ptrDiscipline
  venomExecSemantics venomState venomInst irSupply unitShapeDefs
  o1PassContract execEquivParamBase finite_map list

Theorem ld_env_eval_phis:
  !ins s t s1 H tn.
    EVERY (\i. MEM i (fn_insts fn)) ins /\
    ld_env_agree sites fn H tn s t /\
    s.vs_labels = t.vs_labels /\ s.vs_prev_bb = t.vs_prev_bb /\
    eval_phis s ins = OK s1 ==>
    ?t1. eval_phis t ins = OK t1 /\
      ld_env_agree sites fn (phis_prov s.vs_prev_bb H ins)
        (tn with t_var := phis_taint s.vs_prev_bb tn ins) s1 t1
Proof
  Induct_on `ins`
  >- (simp[eval_phis_def, phis_prov_def, phis_taint_def] >>
      simp[ld_env_agree_def, op_taint_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (qpat_x_assum `eval_phis s (h::ins) = _` mp_tac >>
      simp[Once eval_phis_def, AllCaseEqs()] >> strip_tac >>
      gvs[eval_one_phi_def, AllCaseEqs()] >>
      `MEM val_op h.inst_operands` by metis_tac[resolve_phi_MEM] >>
      `!v. val_op = Var v ==> MEM v (fn_ir_vars fn)` by
        (rpt strip_tac >>
         `?bb. MEM bb fn.fn_blocks /\ MEM h bb.bb_instructions` by
           (fs[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
         simp[fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP,
              PULL_EXISTS, inst_ir_vars_def] >>
         qexistsl_tac [`bb`,`h`] >> simp[] >>
         simp[inst_uses_def] >>
         qpat_x_assum `MEM val_op _` mp_tac >> simp[] >>
         disch_then (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
         simp[operand_vars_APPEND, operand_vars_def, operand_var_def]) >>
      `?v'. eval_operand val_op t = SOME v'` by
        (drule_all ld_env_operand_defined >> simp[] >>
         Cases_on `eval_operand val_op t` >> simp[]) >>
      `s.vs_prev_bb = t.vs_prev_bb` by simp[] >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac `update_var out v' t1` >>
      simp[Once eval_phis_def, eval_one_phi_def] >>
      `~retpc_var fn out ==>
        ld_value_agree sites (op_prov H val_op) (op_taint tn val_op) v v'` by
        (strip_tac >>
         `!y. val_op = Var y ==> ~retpc_var fn y` by
           metis_tac[non_retpc_phi_input, MEM] >>
         drule_all ld_env_operand_value >> simp[]) >>
      Cases_on `op_prov H val_op` >>
      gvs[phis_prov_def, phi_prov_def, phis_taint_def, phi_taint_def,
          ld_env_agree_def, update_var_def, set_prov_def, set_var_taint_def,
          op_taint_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> Cases_on `v'' = out` >>
      gvs[FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  gvs[eval_phis_def, phis_prov_def, phis_taint_def] >>
  simp[ld_env_agree_def, op_taint_def]
QED
