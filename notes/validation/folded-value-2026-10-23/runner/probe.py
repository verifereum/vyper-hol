from pathlib import Path
import hashlib, json, subprocess

root=Path.cwd()
out=root/'.agent-files/folded-value-validation'
b=root/'lowering/defs/bytecode'
hol=out/'hol'
hol.mkdir(exist_ok=True)
stems=[s for s in (b/'folded-value-witnesses.txt').read_text().split() if (out/'oracle'/(s+'.json')).exists() and (out/'oracle'/(s+'.hex')).exists()]
script=root/'.folded_value_validation.sml'
prefix='''fun loading name = (TextIO.output (TextIO.stdErr, "LOAD " ^ name ^ "\\n"); TextIO.flushOut TextIO.stdErr; load name);
val _ = List.app loading ["compileVyperTheory", "supportedProgramTheory", "concretizeMemLocDefsTheory", "codegenReadyComputeTheory", "byteTheory", "optionTheory", "vyperCheckContractFrontendLib", "jsonASTLib", "finite_mapLib", "wordsLib", "Timeout"];
open HolKernel Parse boolLib bossLib;
val _ = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val _ = computeLib.upd_compset (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos]);
'''
body='''
fun probe name = let
  fun status text = memoryStoreWitnessLib.report ("WITNESS " ^ name ^ " " ^ text)
  val path = OS.Path.concat (fixture_root, name ^ ".json")
  val input = vyperCheckContractFrontendLib.prepare_check_input
    {in_deploy=false, address=``0w : address``,
     annotated_ast=JSONDecode.decodeFile jsonASTLib.annotated_ast path,
     storage_layout=JSONDecode.decodeFile jsonASTLib.storage_layout path}
  val _ = status "FRONTEND=ACCEPT"
  fun check mode = ((ignore (vyperCheckContractLib.check_contract
    {in_deploy=mode,address= #address input,modules= #modules input,layouts= #layouts input});
    status ((if mode then "CHECK_DEPLOY=" else "CHECK_RUNTIME=") ^ "ACCEPT"))
    handle exn => status ((if mode then "CHECK_DEPLOY=" else "CHECK_RUNTIME=") ^ "REJECT " ^ General.exnMessage exn))
  val _ = check false
  val _ = check true
  val tops = case #1 (listSyntax.dest_list (#modules input)) of
     [entry] => #2 (pairSyntax.dest_pair entry)
   | _ => raise Fail "expected one module"
  val _ = memoryStoreWitnessLib.write (OS.Path.concat(output_root,name ^ ".tops")) (term_to_string tops)
  val sp = rhs (concl (EVAL ``supported_program ^tops``))
  val _ = status ("SUPPORTED=" ^ term_to_string sp)
  val th = EVAL (memoryStoreWitnessLib.compile_term tops)
  val result = rhs (concl th)
  val _ = memoryStoreWitnessLib.write (OS.Path.concat(output_root,name ^ ".term")) (term_to_string result)
  val _ = status "CHECKED_EVAL=true"
in
  if optionSyntax.is_none result then status "COMPILE=NONE"
  else if not (optionSyntax.is_some result) then status "COMPILE=RESIDUAL"
  else let
    val (deploy,runtime) = pairSyntax.dest_pair(optionSyntax.dest_some result)
    val bytes = "deploy=" ^ memoryStoreWitnessLib.hex_list deploy ^ "\\nruntime=" ^ memoryStoreWitnessLib.hex_list runtime ^ "\\n"
    val _ = memoryStoreWitnessLib.write (OS.Path.concat(output_root,name ^ ".hex")) bytes
    val (ed,er) = pairSyntax.dest_pair(memoryStoreWitnessLib.oracle fixture_root name)
    val _ = status "COMPILE=SOME"
    fun equal left right = aconv boolSyntax.T
      (rhs (concl (EVAL (boolSyntax.mk_eq (left, right)))))
    val _ = status ("DEPLOY_EQUAL=" ^ Bool.toString (equal deploy ed))
    val _ = status ("RUNTIME_EQUAL=" ^ Bool.toString (equal runtime er))
  in () end
end;
fun bounded name = (Timeout.apply (Time.fromSeconds 900) probe name
  handle exn => memoryStoreWitnessLib.report ("WITNESS " ^ name ^ " ERROR=" ^ General.exnMessage exn));
'''
script.write_text(prefix+(b/'eval/evalCompilerBytecodeLib.sml').read_text()+';\n'+(b/'eval/memoryStoreWitnessLib.sml').read_text()+';\nval fixture_root='+json.dumps(str(out/'oracle'))+';\nval output_root='+json.dumps(str(hol))+';\n'+body+'val _ = List.app bounded '+json.dumps(stems)+';\n')
command=['holbuild','--maxheap','12000','run',script.name]
(hol/'run.json').write_text(json.dumps({'argv':command,'witnesses':stems,'revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'script_sha256':hashlib.sha256(script.read_bytes()).hexdigest()},indent=2)+'\n')
with (hol/'probe.log').open('w') as log:
    completed=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
(hol/'exit.json').write_text(json.dumps({'exit':completed.returncode})+'\n')
raise SystemExit(completed.returncode)
