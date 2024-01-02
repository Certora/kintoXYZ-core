// SPDX-License-Identifier: MIT
pragma solidity ^0.8.12;

import { KintoID } from "src/KintoID.sol";

contract KintoIDHarness is KintoID {

    function mint(address account, uint256 tokenId) external {
        _mint(account, tokenId);
    }

    function safeMint(address to, uint256 tokenId) external {
        _safeMint(to, tokenId);
    }

    function safeMint(address to, uint256 tokenId, bytes memory data) external {
        _safeMint(to, tokenId, data);
    }

    function unsafeOwnerOf(uint256 tokenId) external view returns (address) {
        return _ownerOf(tokenId);
    }

    function unsafeGetApproved(uint256 tokenId) external view returns (address) {
        return getApproved(tokenId);
    }

    function tokenURI(uint256 tokenId) public view override returns (string memory) {
        _requireMinted(tokenId);

        return _baseURI();
    }
}