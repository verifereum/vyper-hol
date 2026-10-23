from pathlib import Path
import hashlib, json, platform
from importlib.metadata import version
from eth.chains.base import MiningChain
from eth.db.atomic import AtomicDB
from eth.vm.forks.prague import PragueVM
from eth.exceptions import Revert
from eth_abi import encode
from eth_utils import keccak

out=Path.cwd()/'.agent-files/folded-value-validation'
chain_type=MiningChain.configure(__name__='FoldedValueValidationChain',vm_configuration=((0,PragueVM),))
rows=[]
for stem,typ,value in [('pow_folded_exp','uint256',2**90),('pow_negfold_base','int256',256)]:
    data=keccak(text='f('+typ+')')[:4]+encode([typ],[value])
    for label,root in [('Python',out/'oracle'),('HOL',out/'hol')]:
        path=root/(stem+'.hex')
        if not path.exists():
            raise RuntimeError('No independently evaluated runtime: '+str(path))
        code=bytes.fromhex(next(l.split('=',1)[1] for l in path.read_text().splitlines() if l.startswith('runtime=')))
        chain=chain_type.from_genesis(AtomicDB(),{'difficulty':0,'gas_limit':10_000_000,'timestamp':1},{})
        result=chain.get_vm().execute_bytecode(origin=b'\x01'*20,sender=b'\x01'*20,to=b'\x02'*20,gas_price=0,gas=1_000_000,value=0,data=data,code=code)
        row={'stem':stem,'producer':label,'argument_type':typ,'argument':str(value),'calldata':data.hex(),'runtime_sha256':hashlib.sha256(code).hexdigest(),'runtime_bytes':len(code),'gas_limit':1_000_000,'gas_used':result.get_gas_used(),'is_error':result.is_error,'error_type':type(result.error).__name__ if result.is_error else None,'output':result.output.hex(),'reverted':result.is_error and isinstance(result.error,Revert)}
        rows.append(row)
        print(json.dumps(row),flush=True)
report={'engine':'py-evm','engine_version':version('py-evm'),'vm':'PragueVM','python':platform.python_version(),'eth_abi_version':version('eth-abi'),'executions':rows}
(out/'executions.json').write_text(json.dumps(report,indent=2)+'\n')
assert len(rows)==4 and all(row['reverted'] for row in rows),'Expected four genuine REVERT results'
