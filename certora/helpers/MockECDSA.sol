// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

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