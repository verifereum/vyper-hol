@external
@view
def get_block_hash(n: uint256) -> bytes32:
    return blockhash(n)

@external
@view
def get_blob_hash(index: uint256) -> bytes32:
    return blobhash(index)
