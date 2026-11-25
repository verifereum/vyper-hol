(* Recover a default-free compiler entry from its deployed ABI signature. *)
Theory dispatchedSignatureMemberMods
Ancestors
  dispatchedSignatureOriginMods dispatchedClassifierMods defaultDispatchModsGetter
  e2eModsDefs compileUnit compileVyper constSubstMods vyperABIEntries list pair
Libs
  BasicProvers

val _ = Parse.hide "body";

Theorem deployed_default_free_signature_member:
  source_typing_ok_mods mods exps am tx /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,ics) /\
  ~EXISTS (external_has_defaults o SND) exts /\
  MEM (name,tys) (abi_deployed_signatures mods exps) ==>
  ?tops top mut nr rr args ret body.
    ALOOKUP mods (ALOOKUP exps name) = SOME tops /\ MEM top tops /\
    ((name <> "__default__" /\
      top = FunctionDecl External mut nr rr name args [] ret body) \/
     public_getter_src (ALOOKUP exps name) top =
       SOME (mut,nr,rr,name,args,([]:expr list),ret,body)) /\
    tys = MAP SND args /\
    MEM (ALOOKUP exps name,
      (mut,nr,rr,name,args,([]:expr list),ret,
       subst_consts_stmts_mods (consts_env_mods mods) body)) exts
Proof
  strip_tac >>
  drule_all (SRULE [LET_THM] deployed_signature_selected_module) >>
  disch_then (qx_choosel_then [`tops`,`top`] strip_assume_tac) >>
  `?mut nr rr args dflts ret body.
      (name <> "__default__" /\
       top = FunctionDecl External mut nr rr name args dflts ret body) \/
      public_getter_src (ALOOKUP exps name) top =
        SOME (mut,nr,rr,name,args,dflts,ret,body)` suffices_by
    (disch_then (qx_choosel_then [`mut`,`nr`,`rr`,`args`,`dflts`,`ret`,`body`]
     assume_tac) >>
     drule_all (SRULE [LET_THM] selected_external_member_with_defaults_mods) >>
     simp[subst_consts_fn_mods_def] >> disch_then assume_tac >>
     `dflts = []` by
       (Cases_on `dflts` >> simp[] >>
        qpat_x_assum `~EXISTS _ exts` mp_tac >>
        simp[EXISTS_MEM, combinTheory.o_DEF] >>
        goal_assum (drule_at Any) >>
        simp[external_has_defaults_def, subst_consts_expr_mods_def]) >>
     qpat_x_assum `dflts = []` SUBST_ALL_TAC >>
     qexistsl_tac [`top`,`mut`,`nr`,`rr`,`args`,`ret`,`body`] >>
     fs[subst_consts_expr_mods_def]
     >- (qpat_x_assum `top = FunctionDecl _ _ _ _ _ _ _ _ _` SUBST_ALL_TAC >>
         fs[abi_decl_signatures_def]) >>
     drule tagged_getter_decl_signature >> strip_tac >> gvs[]) >>
  qpat_x_assum `MEM (name,tys) (abi_decl_signatures top)` mp_tac >>
  Cases_on `top` >> simp[abi_decl_signatures_def]
  >- (Cases_on `f` >> simp[abi_decl_signatures_def] >>
      IF_CASES_TAC >> simp[abi_function_signatures_def, MEM_MAP,
                           pairTheory.EXISTS_PROD] >>
      strip_tac >> gvs[] >> metis_tac[])
  >- (Cases_on `v` >> simp[abi_decl_signatures_def, public_getter_src_def] >>
      rpt strip_tac >> gvs[] >> IF_CASES_TAC >> simp[] >>
      pairarg_tac >> simp[]) >>
  Cases_on `v` >> simp[abi_decl_signatures_def, public_getter_src_def] >>
  rpt strip_tac >> gvs[] >> pairarg_tac >> simp[]
QED
