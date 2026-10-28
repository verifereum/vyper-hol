(* Complete fixed #543 body inventory, independently derived from originals.
   No loop/completeness claim for the ordinary #135 frontend or backend. *)
Theory sourceMeaningLocationWitnessTest
Ancestors
  sourceMeaningLocationBody sourceMeaningLocationSource sourceMeaningLocationCode
  sourceMeaningLocationDefs sourceMeaningEnv sourceMeaningRuntime
  sourceModuleFrontendLibTest sourceModuleDecl sourceModuleEnv sourceModuleDefs
  sourceResolveModules sourceResolve sourceSyntax sourceConstEnv sourceConstEval
  sourceConstValue sourceConstBuiltinCompute sourceExprDefs sourceTypeDefs vyperInterpreter vyperAST
  vyperABI vyperContext alist list finite_map
Libs
  sourceMeaningLocationFixturesLib sourceMeaningLocationWitnessLib cv_transLib intLib wordsLib

fun holbuild_extra_deps (_ : string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract/source_syntax",
  "../lowering/defs/bytecode/folded-value-witnesses.txt"];

open sourceMeaningLocationWitnessLib;
(* Kernel-computed hash equations accelerate source evaluation. No compiler
   selectors or expected runtime outputs are computation rewrite rules. *)
val () = List.app (fn text => let
  val bytes = listSyntax.mk_list (List.map (numSyntax.term_of_int o Char.ord)
    (String.explode text),numSyntax.num)
  val th = cv_eval ``source_const_keccak ^bytes``
  in computeLib.add_funs [th] end)
  ["hello","transfer(address,uint256)","foo()","f(uint256)","E(uint256)","x"];
val accepted = ref 0;
val covered = ref 0;

fun check name = let val phase = sourceMeaningLocationFixturesLib.certified_phase name in
  case one "SM_Ok" (rhs(concl phase)) of NONE =>
    if name = "method_id_var" then print "SOURCE_LOCATION_PIN_REJECT method_id_var\n"
    else raise Fail ("unexpected source rejection: " ^ name)
  | SOME retained => let
      val _ = accepted := !accepted + 1
      val program = sourceMeaningLocationFixturesLib.program name
      val registry = some ``source_resolve_program_registry ^program [["main"]]``
      val constants = valOf(one "SCEnv_Resolved" (some ``source_resolve_registry_constants ^registry``))
      val declaration_eq = EVAL ``source_resolve_registry_declarations ^registry``
      val declarations = valOf(one "SOME" (rhs(concl declaration_eq)))
      val dependency_eq = EVAL ``source_const_resolve [] ^declarations``
      val _ = if aconv (rhs(concl dependency_eq)) ``SCEnv_Resolved ^constants`` then ()
        else raise Fail "source dependency environment mismatch"
      val dependencies = MATCH_MP source_meaning_resolve_derivation dependency_eq
      val initializers = MATCH_MP source_meaning_initializer_transport dependency_eq
      val _ = save_thm(name ^ "_constant_dependencies_meaning",CONJ declaration_eq (CONJ dependencies initializers))
      val syntax = hd (#2(strip_comb program))
      val trust = sourceMeaningLocationFixturesLib.trust name
      val ctx = computed ``source_module_context ^trust ^registry ^constants ["main"] ^syntax``
      val decls = hd(#2(strip_comb syntax))
      val global_metadata = EVAL ``source_location_global_metadata ^ctx ^decls``
      val globals = valOf(one "SOME" (rhs(concl global_metadata)))
      val _ = save_thm(name ^ "_original_global_metadata",global_metadata)
      val type_ids = computed ``MAP (\(path,id). (path,case source_type_identity id of
          ST_Ok ty => ty | _ => NoneT)) source_module_primitive_names``
      val emitted = items(sourceMeaningLocationFixturesLib.tops name)
      fun body d = case fields "SD_Function" d of NONE => ()
      | SOME [id,decorators,args,defaults,annotation,original] => let
          val label = stringSyntax.fromHOLstring id
          val parameters = EVAL ``source_module_args ^ctx ^args``
          val params = valOf(one "SM_Ok" (rhs(concl parameters)))
          val returns = EVAL ``source_module_return_type ^ctx ^annotation``
          val ret = valOf(one "SM_Ok" (rhs(concl returns)))
          val _ = save_thm(name ^ "_" ^ label ^ "_original_parameters",CONJ parameters returns)
          val fctx = computed ``source_module_function_context ^ctx ^id ^args ^params``
          val refs = computed ``MAP (\(name,ty).
            ((^ctx).sm_owner ++ [^id;name],(ty,SMR_Local name))) ^params ++ ^globals``
          val (ms,fr,fc,source) = bodies refs type_ids fctx ret original
          val tl = valOf(List.find (fn tl => case fields "FunctionDecl" tl of
            SOME fields => aconv (List.nth(fields,4)) id | NONE => false) emitted)
          val code_body = List.nth(#2(strip_comb tl),8)
          val code = body_code ``FEMPTY:nsid |-> type_args`` ms code_body
          val transport = MATCH_MP (CONJUNCT2(SPEC ``FEMPTY:nsid |-> type_args``
            source_location_body_code_evaluates)) code
          val _ = save_thm(name ^ "_" ^ label ^ "_original_body",source)
          val _ = save_thm(name ^ "_" ^ label ^ "_body_code",code)
          (* The phase retains precisely the freshly decoded original program
             and the declaration containing the related runtime body. *)
          val _ = save_thm(name ^ "_" ^ label ^ "_body_transport",CONJ phase transport)
          in covered := !covered + 1;
            print ("SOURCE_LOCATION_ORIGINAL_BODY " ^ name ^ "." ^ label ^ "\n") end
      | _ => raise Fail "source function syntax arity"
      in List.app body (items decls) end end;

val () = List.app check sourceMeaningLocationFixturesLib.names;
val () = if !accepted = 36 andalso !covered = 40 then ()
  else raise Fail "fixed #543 independent body inventory is incomplete";
val () = print "SOURCE_LOCATION_WITNESS_TOTAL constant_dependencies=36 original_bodies=40 remaining=0\n";
val () = List.app sourceMeaningLocationFixturesLib.audit
  ["sourceMeaningConst","sourceMeaningValue","sourceMeaningDefs","sourceMeaningCode",
   "sourceMeaningElaborate","sourceMeaningEffects","sourceMeaningRuntime","sourceMeaningEnv",
   "sourceMeaningLocationDefs","sourceMeaningLocationCode","sourceMeaningLocationSource",
   "sourceMeaningLocationBody","sourceMeaningLocationWitnessTest"];
