// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

contract BytesLibMock {
    struct VRS {
        uint8 v;
        bytes32 r;
        bytes32 s;
    }
    /// Full signature hash => position => VRS
    mapping(bytes32 => mapping(uint256 => VRS)) private _extractSig;

    function extractSignature(bytes32 signatureHash, uint256 position) external view returns (bytes memory) {
        VRS storage _vrs = _extractSig[signatureHash][position];
        bytes memory sig = abi.encodePacked(_vrs.v,_vrs.r,_vrs.s);
        return sig;
    }
}

contract MockECDSA {

    mapping(bytes32 => mapping(bytes32 => address)) private _recover;

    function recoverMock(bytes32 hash, bytes memory signature) external view returns (address signer) {
        require (signature.length == 65, "Invalid signature length");
        bytes32 sigHash = keccak256(abi.encodePacked(signature));
        signer = _recover[hash][sigHash];
        
        // If the signature is valid (and not malleable), return the signer address
        if (signer == address(0)) {
            revert("InvalidSignature");
        }

        return signer;
    }
}