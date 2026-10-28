Theory sourceMeaningCompile
Ancestors
  sourceMeaningDispatch sourceMeaningDecl sourceMeaningCall sourceMeaningCallDefs
  sourceMeaningProgram sourceMeaningProgramDefs sourceModuleCompile sourceModuleElaborate
  sourceModuleDecl sourceModuleEnv sourceModuleDefs sourceResolveModules sourceSyntax
  vyperTypeContract vyperInterpreter vyperState vyperContext compileVyper alist list

(* Original-source compiler composition. The independent module derivation is
   the semantic domain, not an opaque runtime-readiness assumption. The exact
   shared nominal-type environment is explicit: supplied frontend type metadata
   is not silently equated with the deployed runtime type environment.
   This theorem transports source calls to the checked/compiled Vyper program;
   bytecode execution still requires the existing lower theorem's hypotheses. *)
Theorem source_meaning_compile_program:
  source_module_compile fuel trust keys program layouts address finalizer policy =
    SM_Ok (retained,art,bytes) ==>
  retained_source retained = program /\
  check_contract T layouts address (retained_executable retained) = SOME art /\
  ?tops registry constants signatures.
    retained_executable retained = [(NONE,tops)] /\
    compile_vyper finalizer policy tops = SOME bytes /\
    source_resolve_program_registry program keys = SOME registry /\
    source_meaning_constants registry constants /\
    !owner syntax. MEM (owner,syntax) registry ==>
    ?bindings ctx.
      ctx = ((source_module_body_context trust registry constants signatures owner syntax)
        with sm_bindings := bindings) /\
      source_module_bodies fuel ctx trust.smt_slots syntax = SM_Ok tops /\
      !meanings. source_meaning_module ctx syntax meanings ==>
        LIST_REL (source_meaning_decl_code ctx.sm_env.type_defs) meanings tops /\
        (type_env_all_modules [(NONE,tops)] = ctx.sm_env.type_defs ==>
          (!orc am tx.
            ALOOKUP am.sources tx.target = SOME [(NONE,tops)] /\
            ALOOKUP am.exports tx.target = NONE ==>
            call_external orc am tx = source_meaning_call orc am tx meanings) /\
          (!orc am tx exps.
            load_contract orc am tx [(NONE,tops)] exps =
              source_meaning_load orc am tx [(NONE,tops)] exps meanings))
Proof
  strip_tac >> drule source_module_compile_equations >> strip_tac >> simp[] >>
  drule source_meaning_elaborate_member >> strip_tac >>
  qexistsl_tac [`registry`,`constants`,`signatures`] >> simp[] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule_all >> strip_tac >>
  gvs[] >> qexists_tac `bindings` >> simp[] >>
  rpt gen_tac >> strip_tac >> drule_all source_meaning_module_transport >> strip_tac >>
  gvs[] >> disch_tac >> conj_tac >> rpt gen_tac
  >- (strip_tac >> irule source_meaning_call_transport >> simp[]) >>
  irule source_meaning_load_transport >> simp[]
QED
