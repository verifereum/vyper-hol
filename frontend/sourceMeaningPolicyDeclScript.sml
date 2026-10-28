Theory sourceMeaningPolicyDecl
Ancestors
  sourceMeaningDecl sourceMeaningStmt sourceMeaningCall sourceMeaningCallDefs sourceMeaningDefs
  sourceMeaningPolicy sourceMeaningProgram sourceModuleElaborate sourceModuleDecl sourceModuleDefs sourceSyntax vyperAST list

(* Preserved parser policy acts on SOURCE declaration meanings. Pure functions
   have no lock; external ordinary functions inherit the explicitly supplied
   default unless their original decorators opt out. *)
Definition source_meaning_policy_declaration_def:
  source_meaning_policy_declaration policy declaration
    (SDM_Function vis mut nr raw name args defaults ret body) =
      SDM_Function vis mut
        (mut <> Pure /\ (nr \/ (source_module_nonreentrant_default policy /\
          vis = External /\ ~MEM (SX_Name "reentrant")
            (case declaration of SD_Function n ds a d r b => ds | _ => []))))
        raw name args defaults ret body /\
  source_meaning_policy_declaration policy declaration (SDM_Constant name ty lit) =
    SDM_Constant name ty lit /\
  source_meaning_policy_declaration policy declaration (SDM_Aggregate name ty sv) =
    SDM_Aggregate name ty sv
End

Theorem source_meaning_policy_declaration_transport:
  source_meaning_declaration ctx declaration meaning /\
  ~source_module_declaration_only policy /\
  source_module_policy_body fuel ctx slots policy declaration = SM_Ok emitted ==>
  ?tl. emitted = [tl] /\
    source_meaning_decl_code ctx.sm_env.type_defs
      (source_meaning_policy_declaration policy declaration meaning) tl
Proof
  strip_tac >>
  `?bodies. source_module_body fuel ctx slots declaration = SM_Ok bodies /\
    ?tls. source_module_policy_signature fuel ctx slots policy declaration = SM_Ok tls /\
      emitted = (case declaration of SD_Function n ds a d r b =>
        MAP (\tl. case (tls,tl) of
          ([FunctionDecl vis mut nr raw id ps defs ret ss],
           FunctionDecl bv bm bn br bi bp bd bt bs) =>
            FunctionDecl bv bm nr br bi bp bd bt bs | _ => tl) bodies
        | _ => bodies)` by
    (Cases_on `declaration` >>
     gvs[source_module_policy_body_def, source_module_policy_signature_def,
       source_module_body_def, source_meaning_bind_success] >> metis_tac[]) >>
  drule_all source_meaning_declaration_transport >> strip_tac >> gvs[] >>
  qpat_x_assum `source_meaning_declaration _ _ _` mp_tac >>
  simp[Once source_meaning_declaration_cases] >> strip_tac >>
  gvs[source_module_policy_signature_def, source_module_signature_def,
    source_meaning_bind_success, source_meaning_decl_code_def,
    source_meaning_policy_declaration_def]
QED

Theorem source_meaning_policy_bodies_member:
  source_module_policy_bodies fuel ctx slots policy syntax = SM_Ok tops /\
  MEM declaration (source_module_declarations syntax) ==>
  ?emitted. source_module_policy_body fuel ctx slots policy declaration = SM_Ok emitted /\
    (!tl. MEM tl emitted ==> MEM tl tops)
Proof
  simp[source_module_policy_bodies_def, source_meaning_bind_success] >> strip_tac >> gvs[] >>
  drule_all source_meaning_collect_member >> strip_tac >>
  qexists_tac `y` >> simp[MEM_FLAT] >> metis_tac[]
QED

(* The general public policy phase now feeds declaration semantics directly,
   including the preserved lock policy. No policy-free phase success is used. *)
Theorem source_meaning_policy_program_transport:
  source_module_elaborate fuel trust policies keys program = SM_Ok retained ==>
  ?registry constants signatures.
    source_meaning_constants registry constants /\
    !owner syntax declaration.
      MEM (owner,syntax) registry /\
      MEM declaration (source_module_declarations syntax) ==>
      ?bindings src tops emitted.
        let ctx = (source_module_policy_body_context trust policies registry constants signatures
          owner syntax) with sm_bindings := bindings in
        source_module_policy_body fuel ctx trust.smt_slots
          (source_module_policy_for policies owner) declaration = SM_Ok emitted /\
        MEM (src,tops) (retained_executable retained) /\
        (!meaning. source_meaning_declaration ctx declaration meaning /\
          ~source_module_declaration_only (source_module_policy_for policies owner) ==>
          ?tl. emitted = [tl] /\ MEM tl tops /\
            source_meaning_decl_code ctx.sm_env.type_defs
              (source_meaning_policy_declaration (source_module_policy_for policies owner)
                declaration meaning) tl)
Proof
  strip_tac >> drule source_meaning_policy_elaborate_member >> strip_tac >>
  qexistsl_tac [`registry`,`constants`,`signatures`] >> simp[] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  drule_all source_meaning_policy_bodies_member >> strip_tac >>
  qexistsl_tac [`bindings`,`src`,`tops`,`emitted`] >> simp[] >>
  rpt strip_tac >> drule_all source_meaning_policy_declaration_transport >>
  strip_tac >> gvs[]
QED
